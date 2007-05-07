use ExtUtils::MakeMaker;

###----------------------------------------------------------------###
#  Copyright 2007 - Paul Seamons                                     #
#  Distributed under the GNU General Public License without warranty #
###----------------------------------------------------------------###

WriteMakefile(
              NAME          => "Template::Parser::CET",
              AUTHOR        => "Paul Seamons",
              ABSTRACT_FROM => "lib/Template/Parser/CET.pm",
              VERSION_FROM  => "lib/Template/Parser/CET.pm",
              INSTALLDIRS   => 'site',
              PREREQ_PM  => {
                  Template            => 0,
                  'CGI::Ex::Template' => '2.11',
              },

              dist          => {
                DIST_DEFAULT => 'all tardist',
                COMPRESS     => 'gzip -vf',
                SUFFIX       => '.gz',
              },
              
              clean          => {
                FILES        => '*~',
              },
              
              realclean         => {
                FILES        => '*~',
              },
              );

package MY;

sub postamble {
  return qq^
    
pm_to_blib: README

README: \$(VERSION_FROM)
	pod2text \$(VERSION_FROM) > README
^;
}

1;