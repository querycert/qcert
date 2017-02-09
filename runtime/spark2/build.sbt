name := "qcert-spark2-runtime"

organization := "org.qcert"

version := "0.1.0-SNAPSHOT"

scalaVersion := "2.11.8"

libraryDependencies += "org.apache.spark" %% "spark-core" % "2.1.0" % "provided"
libraryDependencies += "org.apache.spark" %% "spark-sql" % "2.1.0" % "provided"
libraryDependencies += "com.google.code.gson" % "gson" % "2.7"
