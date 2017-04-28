
organization := "org.kframework.k"

name := "kore"

scalaVersion := "2.12.2"

version := "1.0-SNAPSHOT"

resolvers += "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots"

libraryDependencies += "junit" % "junit" % "4.11" % "test"

libraryDependencies += "org.apache.commons" % "commons-lang3" % "3.3.2"

libraryDependencies += "commons-io" % "commons-io" % "2.4"
