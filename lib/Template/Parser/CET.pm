package Template::ParserCET;

=head1 NAME

Template::ParserCET - CGI::Ex::Template based parser

=cut

use vars qw($TEMP_VARNAME);
use strict;
use warnings;
use CGI::Ex::Template 2.11;
use CGI::Ex::Dump qw(debug dex_trace);

###----------------------------------------------------------------###
### new with a little bit of wrangling to keep the
### Template::Grammar from being loaded.

BEGIN {
    $INC{'Template/Grammar.pm'} = 1;

    $TEMP_VARNAME = 'template_parser_cet_temp_varname';
};

use base qw(Template::Parser CGI::Ex::Template);

sub new {
    my $class  = shift;
    my $config = $_[0] && UNIVERSAL::isa($_[0], 'HASH') ? shift(@_) : { @_ };

    local $config->{'GRAMMAR'} = {LEXTABLE => 1, STATES => 1, RULES => 1};

    return $class->SUPER::new($config);
}

###----------------------------------------------------------------###
### these are the only overridden methods from Parser

### use CGI::Ex::Templates parser
sub split_text {
    my ($self, $text) = @_;

    my $doc = $self->{'_component'} = {
        _content => \$text,
    };

    $self->{'_parse_error'} = undef;

    my $tree = eval { $self->parse_tree(\$text) } || do { # errors die
        # return an empty tree - we are delaying reporting the error until Parser gives us more information
        $self->{'_parse_error'} = $@;
        [];
    };

    return $tree;
}

### turn the output from CGI::Ex::Template into a real TT compiled template
sub _parse {
    my ($self, $tree, $info) = @_;

    ### similar in spirit to CGI::Ex::Template->execute_tree - but outputs a TT2 compiled perl template

    # fixup the component - so node_info can get the right info
    my $ref = $self->{'_component'} || die "Missing _component handshake from split_text";
    $ref->{'name'}    = $info->{'name'};
    $ref->{'modtime'} = $info->{'time'};

    # we can throw the error - now that Parser has given us more infomration
    if (my $err = delete $self->{'_parse_error'}) {
        $err->doc($ref) if UNIVERSAL::can($err, 'doc') && ! $err->doc;
        die $err;
    }

    local $self->{'_debug'} = $info->{'DEBUG'} || undef;
    my $doc = $self->{'FACTORY'}->template($self->compile_block($tree));

#    print "--------------------------$ref->{name}--------------------------------\n";
#    print $doc;
#    print "--------------------------$ref->{name}--------------------------------\n";
    return $doc;
}

###----------------------------------------------------------------###

### takes a tree of DIRECTIVES
### and returns a TT block
sub compile_block {
    my ($self, $tree) = @_;

    # node contains (0: DIRECTIVE,
    #                1: start_index,
    #                2: end_index,
    #                3: parsed tag details,
    #                4: sub tree for block types
    #                5: continuation sub trees for sub continuation block types (elsif, else, etc)
    #                6: flag to capture next directive
    my @doc;
    for my $node (@$tree) {

        # text nodes are just the bare text
        if (! ref $node) {
            my $result = $self->{'FACTORY'}->textblock($node);
            push @doc, $result if defined $result;
            next;
        }

        # add debug info
        if ($self->{'_debug'}) {
            my $info = $self->node_info($node);
            my ($file, $line, $text) = @{ $info }{qw(file line text) };
            s/([\'\\])/\\$1/g for $file, $text;
            my $result = $self->{'FACTORY'}->debug([["'msg'"],[["file => '$file'", "line => $line", "text => '$text'"]]]);
            push @doc, $result if defined $result;
        }

        # get method to call
        my $directive = $node->[0];
        $directive = 'FILTER' if $directive eq '|';
        next if $directive eq '#';
        my $method = "compile_$directive";

        my $result = $self->$method($node->[3], $node);
        push @doc, $result if defined $result;
    }

    my $doc = $self->{'FACTORY'}->block(\@doc);

#    print $doc;
    return $doc;
}

###----------------------------------------------------------------###

sub compile_named_args {
    my $self = shift;
    my $args = shift;
    my ($named, @positional) = @$args;

    # [[undef, '{}', 'key1', 'val1', 'key2', 'val2'], 0]
    my @named;
    $named = $named->[0];
    my (undef, $op, @the_rest) = @$named;
    while (@the_rest) {
        my $key = shift @the_rest;
        my $val = @the_rest ? $self->compile_expr(shift @the_rest) : 'undef';
        $key = $key->[0] if ref($key) && @$key == 2 && ! ref $key->[0]; # simple keys can be set in place
        if (! ref $key) {
            $key = $self->compile_expr($key);
            push @named, "$key => $val";
        } else {
            ### this really is the way TT does it - pseudo assignment into a hash
            ### with a key that gets thrown away - but "getting" the value assigns into the stash
            ### scary and gross
            push @named, "'_' => ".$self->compile_expr($key, $val);
        }
    }

    return [\@named, (map { $self->compile_expr($_) } @positional)];
}

sub compile_args {
    my ($self, $args) = @_;
    return '[]' if ! $args;
    return '['. join(", ", map { $self->compile_expr($_) } @$args) .']';
}

### takes variables or expressions and translates them
### into the language that compiled TT templates understand
### it will recurse as deep as the expression is deep
### foo                      :   'foo'
### ['foo', 0]               : $stash->get('foo')
### ['foo', 0] = ['bar', 0]  : $stash->set('foo', $stash->get('bar'))
### [[undef, '+', 1, 2], 0]  : do { no warnings; 1 + 2 }
sub compile_expr {
    my ($self, $var, $val, $default) = @_;
    my $ARGS = {};
    my $i    = 0;
    my $return_ref = delete $self->{'_return_ref_ident'}; # set in compile_operator

    ### return literals
    if (! ref $var) {
        if ($val) { # allow for bare literal setting [% 'foo' = 'bar' %]
            $var = [$var, 0];
        } else {
            return $var if $var =~ /^-?[1-9]\d{0,13}(?:|\.0|\.\d{0,13}[1-9])$/; # return unquoted numbers if it is simple
            $var =~ s/\'/\\\'/g;
            return "'$var'";  # return quoted items - if they are simple
        }
    }

    ### determine the top level of this particular variable access
    my @ident;
    my $name = $var->[$i++];
    my $args = $var->[$i++];
    my $use_temp_varname;
    if (ref $name) {
        if (! defined $name->[0]) { # operator
            my $op_val = '('. $self->compile_operator($name) .')';
            return $op_val if $i >= @$var;
            $use_temp_varname = "do {\n  ".$self->{'FACTORY'}->assign(["'$TEMP_VARNAME'", 0], $op_val).";\n  ";
            push @ident, "'$TEMP_VARNAME'";
        } else { # a named variable access (ie via $name.foo)
            push @ident, $self->compile_expr($name);
        }
    } elsif (defined $name) {
        if ($ARGS->{'is_namespace_during_compile'}) {
            #$ref = $self->{'NAMESPACE'}->{$name};
        } else {
            $name =~ s/\'/\\\'/g;
            push @ident, "'$name'";
        }
    } else {
        return '';
    }

    ### add args
    if (! $args) {
        push @ident, 0;
    } else {
        push @ident, ("[" . join(",\n", map { $self->compile_expr($_) } @$args) . "]");
    }

    ### now decent through the other levels
    while ($i < @$var) {
        ### descend one chained level
        my $was_dot_call = $ARGS->{'no_dots'} ? 1 : $var->[$i++] eq '.';
        $name            = $var->[$i++];
        $args            = $var->[$i++];

        if ($was_dot_call) {
            if (ref $name) {
                if (! defined $name->[0]) { # operator
                    push @ident, '('. $self->compile_operator($name) .')';
                } else { # a named variable access (ie via $name.foo)
                    push @ident, $self->compile_expr($name);
                }
            } elsif (defined $name) {
                if ($ARGS->{'is_namespace_during_compile'}) {
                    #$ref = $self->{'NAMESPACE'}->{$name};
                } else {
                    $name =~ s/\'/\\\'/g;
                    push @ident, "'$name'";
                }
            } else {
                return '';
            }

            if (! $args) {
                push @ident, 0;
            } else {
                push @ident, ("[" . join(",\n", map { $self->compile_expr($_) } @$args) . "]");
            }

        # chained filter access
        } else {
            # resolve and cleanup the name
            if (ref $name) {
                if (! defined $name->[0]) { # operator
                    $name = '('. $self->compile_operator($name) .')';
                } else { # a named variable access (ie via $name.foo)
                    $name = $self->compile_expr($name);
                }
            } elsif (defined $name) {
                if ($ARGS->{'is_namespace_during_compile'}) {
                    #$ref = $self->{'NAMESPACE'}->{$name};
                } else {
                    $name =~ s/\'/\\\'/g;
                    $name = "'$name'";
                }
            } else {
                return '';
            }

            # get the ident to operate on
            my $ident;
            if ($use_temp_varname) {
                $ident = $use_temp_varname
                    ."my \$val = ".$self->{'FACTORY'}->ident(\@ident).";\n  "
                    .$self->{'FACTORY'}->assign(["'$TEMP_VARNAME'", 0], 'undef').";\n  "
                    ."\$val; # return of the do\n  }";
            } else {
                $ident = $self->{'FACTORY'}->ident(\@ident);
            }

            # get args ready
            my $filter_args = $args ? [[], map {$self->compile_expr($_)} @$args] : [[]];

            # return the value that is able to run the filter
            my $block = "\$output = $ident;";
            my $filt_val = "do { my \$output = '';\n". $self->{'FACTORY'}->filter([[$name], $filter_args], $block) ." \$output;\n }";
            $use_temp_varname = "do {\n  ".$self->{'FACTORY'}->assign(["'$TEMP_VARNAME'", 0], $filt_val).";\n  ";

            @ident = ("'$TEMP_VARNAME'", 0);
        }
    }

    # handle captures
    if ($self->{'_return_capture_ident'}) {
        die "Can't capture to a variable with filters (@ident)" if $use_temp_varname;
        die "Can't capture to a variable with a set value"      if $val;
        return \@ident;

    # handle refence getting
    } elsif ($return_ref) {
        die "Can't get reference to a variable with filters (@ident)" if $use_temp_varname;
        die "Can't get reference to a variable with a set value"      if $val;
        return $self->{'FACTORY'}->identref(\@ident);

    # handle setting values
    } elsif ($val) {
        return $self->{'FACTORY'}->assign(\@ident, $val, $default);

    # handle inline filters
    } elsif ($use_temp_varname) {
        return $use_temp_varname
            ."my \$val = ".$self->{'FACTORY'}->ident(\@ident).";\n  "
            .$self->{'FACTORY'}->assign(["'$TEMP_VARNAME'", 0], 'undef').";\n  "
            ."\$val; # return of the do\n  }";

    # finally - normal getting
    } else {
        return $self->{'FACTORY'}->ident(\@ident);
    }
}

### plays operators
### [[undef, '+', 1, 2], 0]  : do { no warnings; 1 + 2 }
### unfortunately we had to provide a lot of perl
### here ourselves which means that Jemplate can't
### use this parser directly without overriding this method
sub compile_operator {
    my $self = shift;
    my $args = shift;
    my (undef, $op, @the_rest) = @$args;
    $op = lc $op;

    $op = ($op eq 'mod') ? '%'
        : ($op eq 'pow') ? '**'
        : ($op eq '==' ) ? 'eq'
        : ($op eq '!=' ) ? 'ne'
        :                  $op;

    if ($op eq '{}') {
        return '{}' if ! @the_rest;
        my $out = "{\n";
        while (@the_rest) {
            my $key = $self->compile_expr(shift @the_rest);
            my $val = @the_rest ? $self->compile_expr(shift @the_rest) : 'undef';
            $out .= "     $key => $val,\n";
        }
        $out .= "}";
        return $out;
    } elsif ($op eq '[]') {
        return "[".join(",\n     ", (map { $self->compile_expr($_) } @the_rest))."]";
    } elsif ($op eq '~' || $op eq '_') {
        return "(''.". join(".\n    ", map { $self->compile_expr($_) } @the_rest).")";
    } elsif ($op eq '=') {
        return $self->compile_expr($the_rest[0], $self->compile_expr($the_rest[1]));

    # handle assignment operators
    } elsif ($CGI::Ex::Template::OP_ASSIGN->{$op}) {
        $op =~ /^([^\w\s\$]+)=$/ || die "Not sure how to handle that op $op";
        my $short = ($1 eq '_' || $1 eq '~') ? '.' : $1;
        return $self->compile_expr($the_rest[0], "do { no warnings; "
                                   .$self->compile_expr($the_rest[0]) ." $short ". $self->compile_expr($the_rest[1]) ."; }");

    } elsif ($op eq '++') {
        my $is_postfix = $the_rest[1] || 0; # set to 1 during postfix
        return "do { no warnings;\nmy \$val = 0 + ".$self->compile_expr($the_rest[0]).";\n"
            .$self->compile_expr($the_rest[0], "\$val + 1").";\n"
            ."$is_postfix ? \$val : \$val + 1;\n}";

    } elsif ($op eq '--') {
        my $is_postfix = $the_rest[1] || 0; # set to 1 during postfix
        return "do { no warnings;\nmy \$val = 0 + ".$self->compile_expr($the_rest[0]).";\n"
            .$self->compile_expr($the_rest[0], "\$val - 1").";\n"
            ."$is_postfix ? \$val : \$val - 1;\n}";

    } elsif ($op eq 'div' || $op eq 'DIV') {
        return "do { no warnings;\n int(".$self->compile_expr($the_rest[0])." / ".$self->compile_expr($the_rest[1]).")}";

    } elsif ($op eq '?') {
        return "do { no warnings;\n " .$self->compile_expr($the_rest[0])
            ." ? ".$self->compile_expr($the_rest[1])
            ." : ".$self->compile_expr($the_rest[2])." }";

    } elsif ($op eq '\\') {
        return do { local $self->{'_return_ref_ident'} = 1; $self->compile_expr($the_rest[0]) };

    } elsif ($op eq 'qr') {
        return $the_rest[1] ? "qr{(?$the_rest[1]:$the_rest[0])}" : "qr{$the_rest[0]}";

    } elsif (@the_rest == 1) {
        return $op.$self->compile_expr($the_rest[0]);
    } else {
        return "do { no warnings; ".$self->compile_expr($the_rest[0])." $op ".$self->compile_expr($the_rest[1])."}";
    }
}

### takes an already parsed identity
### and strips it of args and outputs a string
### so that the passing mechanism of Template::Directive
### can hand off to set or get which will reparse again - wow and sigh
sub compile_ident_str_from_cet {
    my ($self, $ident) = @_;
    return ''     if ! defined $ident;
    return $ident if ! ref $ident;
    return ''     if ref $ident->[0] || ! defined $ident->[0];

    my $i = 0;
    my $str = $ident->[$i++];
    $i++; # for args;

    while ($i < @$ident) {
        my $dot = $ident->[$i++];
        return $str if $dot ne '.';
        return $str if ref $ident->[$i] || ! defined $ident->[$i];
        $str .= ".". $ident->[$i++];
        $i++; # for args
    }
    return $str;
}

### references take the data in yet
### another form
sub compile_ident_str_from_tt {
    my ($self, $ident) = @_;
    return ''     if ! defined $ident;
    return $ident if ! ref $ident;
    return ''     if ! defined $ident->[0];

    my $i = 0;
    my $str = $ident->[$i++];
    $i++; # for args;

    while ($i < @$ident) {
        my $dot = $ident->[$i++];
        return $str if $dot ne '.';
        return $str if ref $ident->[$i] || ! defined $ident->[$i];
        $str .= ".". $ident->[$i++];
        $i++; # for args
    }
    return $str;

}

###----------------------------------------------------------------###
### everything below this point are the output of DIRECTIVES - as much as possible we
### try to use the facilities provided by Template::Directive

sub compile_BLOCK {
    my ($self, $name, $node) = @_;
    return $self->define_block($name, $self->{'FACTORY'}->template($self->compile_block($node->[4])));
}

sub compile_BREAK { shift->{'FACTORY'}->break }

sub compile_CALL {
    my ($self, $ident) = @_;
    return $self->{'FACTORY'}->call($self->compile_expr($ident));
}

sub compile_CLEAR {
    my $self = shift;
    return $self->{'FACTORY'}->clear;
}

sub compile_DEBUG {
    my ($self, $ref) = @_;
    my @options = "'$ref->[0]'";
    if ($ref->[0] eq 'format') {
        my $format = $ref->[1];
        $format =~ s/([\'\\])/\\$1/g;
        push @options, "'$format'";
    } elsif (defined $self->{'_debug'}) { # defined if on at beginning
        if ($ref->[0] eq 'on') {
            $self->{'_debug'} = 1;
        } elsif ($ref->[0] eq 'off') {
            $self->{'_debug'} = 0;
        }
    }
    return $self->{'FACTORY'}->debug([\@options, [[]]]);
}

sub compile_DEFAULT {
    my ($self, $set, $node) = @_;
    return $self->compile_SET($set, $node, 1);
}

sub compile_DUMP {
    my ($self, $args, $node) = @_;
    my $info = $self->node_info($node);

    return $self->{'FACTORY'}->dump($self->compile_named_args($args), $info->{'file'}, $info->{'line'}, \$info->{'text'});
}

sub compile_END { '' }

sub compile_FILTER {
    my ($self, $ref, $node) = @_;
    my ($alias, $filter) = @$ref;

    my ($filt_name, $args) = @$filter; # doesn't support CGI::Ex::Template chained filters

    $args = ! $args ? [[]] : [[], map { $self->compile_expr($_) } @$args];

    $self->{'FACTORY'}->filter([[$self->compile_expr($filt_name)],
                                $args,
                                $self->compile_expr($alias)
                                ],
                               $self->compile_block($node->[4]));
}

sub compile_FOR { shift->compile_FOREACH(@_) }

sub compile_FOREACH {
    my ($self, $ref, $node) = @_;
    my ($var, $items) = @$ref;
    if ($var) {
        #debug $var;
        $var = $var->[0];
    }

    $items = $self->compile_expr($items);

    local $self->{'loop_type'} = 'FOREACH';
    return $self->{'FACTORY'}->foreach($var, $items, [[]], $self->compile_block($node->[4]));
}

sub compile_GET {
    my ($self, $ident) = @_;
    return $self->{'FACTORY'}->get($self->compile_expr($ident));
}

sub compile_IF {
    my ($self, $ref, $node, $unless) = @_;

    my $expr  = $self->compile_expr($ref);
    $expr = "!$expr" if $unless;

    my $block = $self->compile_block($node->[4]);

    my @elsif;
    my $had_else;
    while ($node = $node->[5]) { # ELSE, ELSIF's
        if ($node->[0] eq 'ELSE') {
            if ($node->[4]) {
                push @elsif, $self->compile_block($node->[4]);
                $had_else = 1;
            }
            last;
        }
        my $_expr  = $self->compile_expr($node->[3]);
        my $_block = $self->compile_block($node->[4]);
        push @elsif, [$_expr, $_block];
    }
    push @elsif, undef if ! $had_else;

    return $self->{'FACTORY'}->if($expr, $block, \@elsif);
}

sub compile_INCLUDE {
    my ($self, $ref, $node) = @_;

    my ($named, @files) = @{ $self->compile_named_args($ref) };

    return $self->{'FACTORY'}->include([\@files, [$named]]);
}

sub compile_INSERT {
    my ($self, $ref, $node) = @_;

    my ($named, @files) = @{ $self->compile_named_args($ref) };

    return $self->{'FACTORY'}->insert([\@files, [$named]]);
}

sub compile_LAST {
    my $self = shift;
    my $type = $self->{'loop_type'} || '';
    return "last LOOP;\n" if $type eq 'WHILE' || $type eq 'FOREACH';
    return "last;\n"; # the grammar nicely hard codes the choices
    return "last;\n";
}

sub compile_MACRO {
    my ($self, $ref, $node, $out_ref) = @_;
    my ($name, $args) = @$ref;

    $name = $self->compile_ident_str_from_cet($name);
    $args = [map {$self->compile_ident_str_from_cet($_)} @$args] if $args;

    ### get the sub tree
    my $sub_tree = $node->[4];
    if (! $sub_tree || ! $sub_tree->[0]) {
        $self->set_variable($name, undef);
        return;
    } elsif ($sub_tree->[0]->[0] eq 'BLOCK') {
        $sub_tree = $sub_tree->[0]->[4];
    }

    return $self->{'FACTORY'}->macro($name, $self->compile_block($sub_tree), $args);
}

sub compile_META {
    my ($self, $hash, $node) = @_;
    $self->add_metadata([%$hash]) if $hash;
    return '';
}

sub compile_NEXT {
    my $self = shift;
    my $type = $self->{'loop_type'} || '';
    return $self->{'FACTORY'}->next if $type eq 'FOREACH';
    return "next LOOP;\n" if $type eq 'WHILE';
    return "next;\n";
}

sub compile_PERL {
    my ($self, $ref, $node) = @_;
    my $block = $node->[4] || return '';
    return $self->{'FACTORY'}->no_perl if ! $self->{'EVAL_PERL'};

    return $self->{'FACTORY'}->perl($self->compile_block($block));
}

sub compile_PROCESS {
    my ($self, $ref, $node) = @_;

    my ($named, @files) = @{ $self->compile_named_args($ref) };

    return $self->{'FACTORY'}->process([\@files, [$named]]);
}

sub compile_RAWPERL {
    my ($self, $ref, $node) = @_;

    return $self->{'FACTORY'}->no_perl if ! $self->{'EVAL_PERL'};

    my $block = $node->[4] || return '';
    my $info  = $self->node_info($node);
    my $txt = '';
    foreach my $chunk (@$block) {
        next if ! defined $chunk;
        if (! ref $chunk) {
            $txt .= $chunk;
            next;
        }
        next if $chunk->[0] eq 'END';
        die "Handling of $chunk->[0] not yet implemented in RAWPERL";
    }

    return $self->{'FACTORY'}->rawperl($txt, $info->{'line'});
}

sub compile_RETURN {
    my $self = shift;
    return $self->{'FACTORY'}->return;
}

sub compile_SET {
    my ($self, $set, $node, $default) = @_;

    my $out = '';
    foreach (@$set) {
        my ($op, $set, $val) = @$_;

        if (! defined $val) { # not defined
            $val = "''";
        } elsif ($node->[4] && $val == $node->[4]) { # a captured directive
            my $sub_tree = $node->[4];
            $sub_tree = $sub_tree->[0]->[4] if $sub_tree->[0] && $sub_tree->[0]->[0] eq 'BLOCK';
            $set = do { local $self->{'_return_capture_ident'} = 1; $self->compile_expr($set) };
            $out .= $self->{'FACTORY'}->capture($set, $self->compile_block($sub_tree));
            next;
        } else { # normal var
            $val = $self->compile_expr($val);
        }

        if ($CGI::Ex::Template::OP_DISPATCH->{$op}) {
            $op =~ /^([^\w\s\$]+)=$/ || die "Not sure how to handle that op $op during SET";
            my $short = ($1 eq '_' || $1 eq '~') ? '.' : $1;
            $val = "do { no warnings;\n". $self->compile_expr($set) ." $short $val}";
        }

        $out .= $self->compile_expr($set, $val, $default).";\n";
    }

    return $out;
}

sub compile_STOP {
    my $self = shift;
    return $self->{'FACTORY'}->stop;
}

sub compile_SWITCH {
    my ($self, $var, $node) = @_;

    my $expr = $self->compile_expr($var);
    ### $node->[4] is thrown away

    my @cases;
    my $default;
    while ($node = $node->[5]) { # CASES
        my $var   = $node->[3];
        my $block = $self->compile_block($node->[4]);
        if (! defined $var) {
            $default = $block;
            next;
        }

        $var = $self->compile_expr($var);
        push @cases, [$var, $block];
    }
    push @cases, $default;

    return $self->{'FACTORY'}->switch($expr, \@cases);
}

sub compile_TAGS { '' } # doesn't really do anything - but needs to be in the parse tree

sub compile_THROW {
    my ($self, $ref) = @_;
    my ($name, $args) = @$ref;

    $name = $self->compile_expr($name);

    $self->{'FACTORY'}->throw([[$name], $self->compile_named_args($args)]);
}

sub compile_TRY {
    my ($self, $foo, $node, $out_ref) = @_;
    my $out = '';

    my $block = $self->compile_block($node->[4]);

    my @catches;
    my $had_final;
    while ($node = $node->[5]) { # FINAL, CATCHES
        if ($node->[0] eq 'FINAL') {
            if ($node->[4]) {
                $had_final = $self->compile_block($node->[4]);
            }
            next;
        }
        my $_expr  = defined($node->[3]) && uc($node->[3]) ne 'DEFAULT' ? $node->[3] : ''; #$self->compile_expr($node->[3]);
        my $_block = $self->compile_block($node->[4]);
        push @catches, [$_expr, $_block];
    }
    push @catches, $had_final;

    return $self->{'FACTORY'}->try($block, \@catches);
}

sub compile_UNLESS {
    return shift->compile_IF(@_);
}

sub compile_USE {
    my ($self, $ref) = @_;
    my ($var, $module, $args) = @$ref;

    $var = $self->compile_expr($var) if defined $var;

    return $self->{'FACTORY'}->use([[$self->compile_expr($module)], $self->compile_named_args($args), $var]);
}

sub compile_VIEW {
    my ($self, $ref, $node) = @_;

    my ($blocks, $args, $viewname) = @$ref;

    $viewname = $self->compile_ident_str_from_cet($viewname);
    $viewname =~ s/\\\'/\'/g;
    $viewname = "'$viewname'";

    my $named = $self->compile_named_args([$args])->[0];

    ### prepare the blocks
    #my $prefix = $hash->{'prefix'} || (ref($name) && @$name == 2 && ! $name->[1] && ! ref($name->[0])) ? "$name->[0]/" : '';
    foreach my $key (keys %$blocks) {
        $blocks->{$key} = $self->{'FACTORY'}->template($self->compile_block($blocks->{$key})); #{name => "${prefix}${key}", _tree => $blocks->{$key}};
    }

    my $block = $self->compile_block($node->[4]);
    my $stuff= $self->{'FACTORY'}->view([[$viewname], [$named]], $block, $blocks);
#    print "---------------------\n". $stuff ."------------------------------\n";
    return $stuff;
}

sub compile_WHILE {
    my ($self, $ref, $node) = @_;

    my $expr  = $self->compile_expr($ref);

    local $self->{'loop_type'} = 'while';
    my $block = $self->compile_block($node->[4]);

    return $self->{'FACTORY'}->while($expr, $block);
}

sub compile_WRAPPER {
    my ($self, $ref, $node) = @_;

    my ($named, @files) = @{ $self->compile_named_args($ref) };

    return $self->{'FACTORY'}->wrapper([\@files, [$named]], $self->compile_block($node->[4]));
}

1;

__END__
