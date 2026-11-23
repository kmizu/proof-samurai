ThisBuild / scalaVersion := "3.8.4"
ThisBuild / organization := "io.proofsamurai"
ThisBuild / version := "0.1.0"

lazy val root = (project in file("."))
  .settings(
    name := "proof-samurai",
    scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
      "-unchecked",
      "-Wunused:imports"
    ),
    libraryDependencies ++= Seq(
      "org.scalameta" %% "munit" % "1.1.1" % Test,
      "org.scala-lang" %% "scala3-compiler" % scalaVersion.value % Test
    ),
    Compile / mainClass := Some("samurai.Main"),
    fork := true
  )
