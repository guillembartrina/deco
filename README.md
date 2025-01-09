# deco

## prerequisites

* This plugin depends on a private fork of the compiler --> https://github.com/guillembartrina/scala3/tree/suspendable<br>
  run `sbt scala3-compiler/publishLocal`

* And on a custom build of the scala-native libraries --> https://github.com/guillembartrina/scala-native/tree/newlib<br>
  run `sbt publish-local-dev 3.6.4-RC1-bin-SNAPSHOT`

## building

* First build the library for the target platform<br>
  run `sbt libraryX/publishLocal` where `X` is one of {`JVM`, `JS`, `Native`}

* Then build the plugin<br>
  run `sbt plugin/publishLocal`

## usage

* First import the library<br>
  `libraryDependencies += "idk.deco" %% "library" % "0.1.0-SNAPSHOT"` for JVM<br>
  or `libraryDependencies += "idk.deco" %%% "library" % "0.1.0-SNAPSHOT"` for JS and Native

* Then enable the plugin<br>
  `autoCompilerPlugins := true` and `addCompilerPlugin("idk.deco" %% "plugin" % "0.1.0-SNAPSHOT")`

* And remember to enable the capture checker in every compilation unit that makes use of the feature<br>
  `import language.experimental.captureChecking`



