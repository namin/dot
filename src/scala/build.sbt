name := "dot"

version := "0.1"

scalaVersion := "2.10.0-RC2"

scalacOptions += "-deprecation"

libraryDependencies <+= scalaVersion { v => "com.googlecode.kiama" % ("kiama_"+v) % "1.4.0-B3"  }

libraryDependencies <+= scalaVersion { v => "org.scalatest" % ("scalatest_"+v) % "1.8" % "test" }

libraryDependencies += "junit" % "junit" % "4.8.1" % "test"