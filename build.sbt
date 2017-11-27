
organization := "org.kframework.k"

name := "kore"

scalaVersion := "2.12.4"

version := "1.2-SNAPSHOT"

resolvers += "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots"

libraryDependencies ++= Seq("junit" % "junit" % "4.11" % "test",
  "org.apache.commons" % "commons-lang3" % "3.3.2",
  "commons-io" % "commons-io" % "2.4",
  "org.scalatest" %% "scalatest" % "3.0.1" % "test")
