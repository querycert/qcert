### Obtaining the ODM Rules dependencies

The ODM rules support requires that you obtain a legal copy of the ODM
Designer component that comes with various versions of ODM.

ODM comes in (at least) two configurations called "ODM Rules" and "ODM
Insights".  Each comes with its own Designer, which in turn supports a
characteristic set of languages.  There are (at least) two license
arrangements: "ODM Classic" has only the Rules configuration and "ODM
Advanced" comes with both Rules and Insights.  There is also ODM in
the cloud, based on the Rules configuration.  We hope that our support
will work with either the Insights Designer or the Rules Designer but
we have only tested it with the Rules Designer and it only covers the
languages that are provided by that Designer.

There is no free version of ODM, but some 30 day free trial programs
will allow you to try out certain versions.  In order to use our
"technical" rule support, you need a binary jar available only with an
ODM Designer.  To use the "designer" rule support, you need to fully
install and utilize an ODM Designer.

One possible route is to sign up for the 30 day free trial of ODM in
the Cloud (https://www.bpm.ibmcloud.com/odm/index.html).  Once you are
authorized for the trial, you can log in to the cloud service and
obtain a copy of the ODM Rules Designer (downloaded and installed on
your own machine).

Once you have a Designer component installed on your machine, the next
step is to find the library called **jrules-engine.jar** and copy it
to a directory in the qcert working tree.  Start by making the
directory

```
jrulesParser/lib
```

if it does not already exist.

If you installed the Designer using ODM in the cloud, there is a copy
of `jrules-engine.jar` in the `studio/lib` directory of the directory
where the Designer is installed.  Simply copy that file into the
`jrulesParser/lib` directory.  If you have some other version of ODM
Rule Designer or Insights Designer, find the location where the ODM
plugins are located and look for a plugin jar whose name starts with
"com.ibm.rules.engine...".  Inside this jar you may find a copy of
jrules-engine.jar.  Unzipping the outer jar into the `jrulesParser`
directory should put a copy of jrules-engine.jar in the `lib`
subdirectory.  Beyond those suggestions, you are on your own.

