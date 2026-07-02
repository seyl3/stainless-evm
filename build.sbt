val scala3Version = "3.7.2"

lazy val root = project
  .in(file("."))
  .enablePlugins(StainlessPlugin)
  .settings(
    name := "stainless-evm",
    version := "0.1.0-SNAPSHOT",
    scalaVersion := scala3Version,
    resolvers += MavenRepository("stainless-local", s"file://${(ThisBuild / baseDirectory).value.getAbsolutePath}/stainless"),
    scalacOptions += "-Wconf:src=.*stainless-library.*:s",
    libraryDependencies += "org.scalameta" %% "munit" % "1.3.2" % Test,
  )
