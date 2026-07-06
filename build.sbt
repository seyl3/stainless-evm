val scala3Version = "3.7.2"

// The verified EVM core. Stainless runs on every compile of this project.
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

// The unverified CLI shell. It depends on the core via compiled bytecode (not
// source), so Stainless never sees it and it can use plain Scala I/O and parsing.
// Run with: sbt "cli/run run 602a60005260206000f3"
lazy val cli = project
  .in(file("cli"))
  .dependsOn(root)
  .settings(
    name := "stainless-evm-cli",
    scalaVersion := scala3Version,
    scalacOptions += "-Wconf:src=.*stainless-library.*:s",
  )
