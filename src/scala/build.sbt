name := "dot"

version := "0.1"

scalaVersion := "2.10.0"

scalacOptions += "-deprecation"

libraryDependencies += "com.googlecode.kiama" %% "kiama" % "1.4.0"

libraryDependencies <+= scalaVersion { v => "org.scalatest" % ("scalatest_"+v) % "2.0.M5" % "test" }

libraryDependencies += "junit" % "junit" % "4.8.1" % "test"