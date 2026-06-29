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

// `evm` references `core` types (e.g. Word256 fields in Stack), and Stainless
// extracts cross-module references from source, not bytecode. So `evm` compiles
// proofs + core sources directly instead of `dependsOn(core)` (which would only
// share bytecode and also double-define the classes).
lazy val evm = project
  .in(file("evm"))
  .enablePlugins(StainlessPlugin)
  .settings(
    name := "evm",
    commonSettings,
    Compile / unmanagedSourceDirectories ++= Seq(
      (ThisBuild / baseDirectory).value / "proofs" / "src" / "main" / "scala",
      (ThisBuild / baseDirectory).value / "core" / "src" / "main" / "scala",
    ),
  )

lazy val root = project
  .in(file("."))
  .aggregate(core, evm)
  .settings(
    name := "stainless-evm",
    commonSettings,
    libraryDependencies += "org.scalameta" %% "munit" % "1.3.2" % Test,
  )
