val scala3Version = "3.7.2"

lazy val commonSettings = Seq(
  scalaVersion := scala3Version,
  version := "0.1.0-SNAPSHOT",
  resolvers += MavenRepository("stainless-local", s"file://${(ThisBuild / baseDirectory).value.getAbsolutePath}/stainless"),
  scalacOptions += "-Wconf:src=.*stainless-library.*:s",
)
lazy val core = project
  .in(file("core"))
  .enablePlugins(StainlessPlugin)
  .settings(
    name := "core",
    commonSettings,
    Compile / unmanagedSourceDirectories +=
      (ThisBuild / baseDirectory).value / "proofs" / "src" / "main" / "scala",
  )

lazy val evm = project
  .in(file("evm"))
  .enablePlugins(StainlessPlugin)
  .dependsOn(core)
  .settings(
    name := "evm",
    commonSettings,
  )

lazy val root = project
  .in(file("."))
  .aggregate(core, evm)
  .settings(
    name := "stainless-evm",
    commonSettings,
    libraryDependencies += "org.scalameta" %% "munit" % "1.3.2" % Test,
  )
