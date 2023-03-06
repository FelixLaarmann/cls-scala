# cls-scala
[![Maven Central](https://img.shields.io/maven-central/v/org.combinators/cls-scala_2.13.svg)](http://search.maven.org/#search%7Cga%7C1%7Cg%3A%22org.combinators%22%20AND%20%22cls-scala%22)
[![build status](https://github.com/combinators/cls-scala/workflows/Test%20code,%20update%20coverage,%20and%20release%20master%20branch/badge.svg?branch=master)](https://github.com/combinators/cls-scala/actions?query=workflow%3A%22Test+code%2C+update+coverage%2C+and+release+master+branch%22)
[![Coverage Status](https://coveralls.io/repos/github/combinators/cls-scala/badge.svg?branch=master)](https://coveralls.io/github/combinators/cls-scala?branch=master)
[![Join the chat at https://gitter.im/combinators/cls-scala](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/combinators/cls-scala)
## The Combinatory Logic Synthesizer (CL)S Framework

This project implements the Combinatory Logic Synthesizer (CL)S framework in Scala.

It is a fork of the original [cls-scala Framework](https://github.com/combinators/cls-scala), extending it with a Boolean Query Language.

The extension is conservative, since it only adds a new package [queries](src/main/scala/org/combinators/cls/queries) 
and an updated [labyrinth-example](examples/src/main/scala/org/combinators/cls/examples/LabyrinthBenchmarkBFCL.scala) to showcase the
new features.

If you just want to get an impression of the new features, the best way would be to clone the repository and open it in an IDE
like IntelliJ or something similar.

## Installation

Clone the repository and run `sbt publishLocal`.

Add the following dependency to your existing sbt project:
```scala
libraryDependencies += "org.combinators" %% "cls-scala" % "<VERSION>"
```
The string `<VERSION>` has to be replaced by the version you want.

Currently, Scala 2.11, 2.12, and 2.13 are supported.

## Examples

Can be found in the [examples project](examples/src/main/scala/org/combinators/cls/examples) and 
the [tests](src/test/scala/org/combinators/cls).


