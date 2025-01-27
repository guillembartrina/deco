
ThisBuild / organization := "idk.deco"

ThisBuild / scalaVersion := "3.7.0-RC1-bin-SNAPSHOT"

lazy val library = crossProject(JVMPlatform, JSPlatform, NativePlatform).crossType(CrossType.Pure).in(file("library"))
  .settings(
    name := "library"
  )

lazy val plugin = project.in(file("plugin"))
  .settings(
    name := "plugin",
    libraryDependencies ++= Seq(
      "org.scala-lang" %% "scala3-compiler" % scalaVersion.value % "provided"
    )
  )

