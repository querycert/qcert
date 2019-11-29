This folder contains the support for "JRules" input to the Q*Cert compiler.

What do we mean by "JRules"?

The name "JRules" does not denote a single language but rather a rule management system, sold by ILog and then
by IBM.  IBM has since renamed this system "Operational Decision Manager" (ODM).  The support in this
directory covers some but not all of the rule languages available with ODM.  ODM provides an eclipse-based
rule authoring IDE called the "Designer" which is a pre-requisite here.

We support "technical rules" (written with a Java-like syntax).  ODM uses the terms "ILog Rule Language"
(IRL), "Advanced Rule Language" (ARL), and "Technical Rule Language" (TRL) variously to denote these kinds of
rules, with small variations.  We provide examples (with suffix .arl) in the data subdirectory.

We also support "business rules" (written in a natural-language like syntax), but you have to author these in
an ODM Designer and successfully build the projects that contain them.  Once you have them, you can find a
compiled form of them inside the Designer workspace.  These can be consumed by Q*cert under the right
circumstances.

Note that our ability to consume JRules languages is an experimental facility developed by researchers and not
the ODM product team.  You cannot expect support from IBM in using this experimental facility, which is
provided ASIS.  ODM APIs and file formats that we depend upon here are not necessarily documented for public
use.  Changes may cause the experimental facility to stop working either temporarily or permanently.

Pre-requisites

To use this support you need a Java 8 SDK and ant.  Both the java and javac commands, as well as the ant
command, must be in the execution path.  You also need a legal copy of an ODM Designer.

ODM comes in (at least) two configurations called "ODM Rules" and "ODM Insights".  Each comes with its own
Designer, which in turn supports a characteristic set of languages.  There are (at least) two license
arrangements: "ODM Classic" has only the Rules configuration and "ODM Advanced" comes with both Rules and
Insights.  There is also ODM in the cloud, based on the Rules configuration.  We hope that our support will
work with either the Insights Designer or the Rules Designer.

There is no free version of ODM, but some 30 day free trial programs will allow you to try out certain
versions.  In order to use our ARL support, you need a binary jar available only with an ODM Designer.  To use
the business rule support, you need to fully install and utilize an ODM Designer.

One possible route is to sign up for the 30 day free trial of ODM in the Cloud
(https://www.bpm.ibmcloud.com/odm/index.html).  Once you are authorized for the trial, you can log in to the
cloud service and obtain a copy of the ODM Rules Designer (downloaded and installed on your own machine).  At
that point you, can enable the support.

Installing / Enabling

1.  If there is no lib subdirectory of this directory, make one.

2.  Obtain a legal copy of jrules-engine.jar and place it in lib.  If you have a legal copy of the Rule
Designer for ODM in the cloud, there is a copy of jrules-engine.jar in the studio/lib directory of the
directory where the Rule Designer is installed.  Simply copy that file into the lib subdirectory here.  If you
have some other version of ODM Rule or Insights Designer, find the location where the ODM plugins are located
and look for a plugin jar whose name starts with "com.ibm.rules.engine...".  Inside this jar you may find a
copy of jrules-engine.jar.  Unzipping the outer jar into this directory should put a copy of jrules-engine.jar
in the lib subdirectory.  Beyond those suggestions, you are on your own.

3.  Type

make

in this directory.  This should first build other Java-based projects in the qcert repository, then fetch
additional (OSS) dependencies, then build the code of this project and export it to the Java services.

4. (Optional) If you are also using the SQL parsing support, this is provided via the Java services as well.  Type

make -C ../sqlParser

to make sure that the most up-to-date SQL parser is included in the Java services that you install in the next
step.

5.  Type

make -C ../javaService install

to package up the Java services for use by the qcert command line tool and the qcert.html web form.

Demonstration

1.  To build all the ARL tests to js and then run them, type 'make all_run' (here).  This also generates
additional files for testing in the qcert.html web form (see below).  One test (test06.arl) is currently
failing.  We believe this may be due to an ODM bug but are not sure.

This way of building uses a separate batch program to translate the tests to the CAMP language before
invoking qcert.  Think of this as an installation validation test.  The remaining demonstration steps show off
how we intend JRules to be used in practice.

2.  To use the qcert command line tool directly on ODM technical or business rules, specify

-source tech_rule

or

-source designer_rule

as part of the command line.  We use 'designer_rule' rather than "business rule" to emphasize that ODM
business rules must be built by an ODM Designer product.  It is the output artifact of that build that is
consumed by qcert.

Various test ARL files (technical rules) are provided in the data subdirectory (with file extension .arl).
For these rules, you must specify a schema using the -schema directive.  Use the provided file testSchema.json
in the data subdirectory.

A schema is not needed for the 'designer_rule' case, but you need to locate the output artifact in a designer
workspace and specify it's path.  Locate your designer workspace.  For each successfully built rule there
should be a file of extension .sem in the output directory of the containing project.

3.  To observe integrated compilation and execution in the www/qcert.html web form:

a.  Start the JavaService in server mode locally.

cd qcert/bin
java -jar javaService.jar -server 9879

b.  Open www/qcert.html in a web browser.

c.  For technical rules,

i. Select the "tech_rule" source type

ii. File-choose an ARL file from the 'data' subdirectory of this directory.

iii. For the schema, file-choose testSchema.json from the 'data' subdirectory of this directory.

iv. For input, you have three choices.

(1) Don't select any input, and don't execute the result.

(2) Use the file testInput in the 'data' subdirectory of this directory.  If it does not exist, you can make
it with 'make data/testInput'.  This is the only choice that works if you will execute with output languages
other than Javascript.

(3) Use the .io file corresponding to the .arl file you loaded in step ii.  This will only exist if you have
previously generated it using the Makefile.  Providing an .io file will cause the execute step to check the
result against data generated by the ODM rule engine.

v.  You can use any output language, but support for self-testing with an .io file is only available for Javascript.

vi. Use the Compile and Execute buttons to observe results.

d.  For ODM business rules authored in designer

i. Locate your designer workspace.  For each successfully built rule there should be a file of extension .sem
in the output directory of the containing project.

ii.  Select the "designer_rule" source type

iii. File-choose a .sem file that you located in step i.  It will appear as gibberish (sorry, it's
binary and is base64 encoded at read-in).

iv. No schema is needed (ODM Designer has an internal schema that it used in building the rule, but it is not
needed for this translation step).

v.  Select an output language and compile.  For execution, you are on your own for input data and checking.
