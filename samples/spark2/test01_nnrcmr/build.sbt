scalaVersion := "2.11.8"

libraryDependencies += "org.qcert" %% "qcert-spark2-runtime" % "0.1.0-SNAPSHOT"
libraryDependencies += "org.apache.spark" %% "spark-core" % "2.1.0" % "provided"
libraryDependencies += "org.apache.spark" %% "spark-sql" % "2.1.0" % "provided"

assemblyMergeStrategy in assembly := {
 case PathList("META-INF", xs @ _*) => MergeStrategy.discard
 case x => MergeStrategy.first
}
