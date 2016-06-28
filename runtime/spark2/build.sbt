name := "spark2runtime"

version := "1.0"

scalaVersion := "2.11.8"

resolvers += "apache-snapshots" at "http://repository.apache.org/snapshots/"

libraryDependencies += "org.apache.spark" %% "spark-core" % "2.0.0-SNAPSHOT"
libraryDependencies += "org.apache.spark" %% "spark-sql" % "2.0.0-SNAPSHOT"
libraryDependencies += "com.google.code.gson" % "gson" % "2.7"