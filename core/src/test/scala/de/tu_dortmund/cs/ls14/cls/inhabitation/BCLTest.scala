package de.tu_dortmund.cs.ls14.cls.inhabitation

import org.scalatest._
import de.tu_dortmund.cs.ls14.cls.types._

class BCLTest extends FunSpec {

  val mapTest =
    Map(
      "map" ->
        Arrow(
          Arrow(Variable("alpha"), Variable("beta")),
          Arrow(
            Constructor("List", Variable("alpha")),
            Constructor("List", Variable("beta"))
          )
        ),
      "l" -> Constructor("List", Constructor("Int")),
      "f" -> Arrow(Constructor("Char"), Constructor("String"))
    )

  val taxonomy =
    Taxonomy("Char")
      .addSubtype("Int")
      .merge(Taxonomy("String"))

  def addAll(k: Kinding): Kinding =
    k.addOption(Constructor("Char"))
     .addOption(Constructor("Int"))
     .addOption(Constructor("String"))

  val kinding =
    addAll(Kinding(Variable("alpha"))).merge(addAll(Kinding(Variable("beta"))))

  val Gamma = new BoundedCombinatoryLogic(kinding, SubtypeEnvironment(taxonomy), mapTest)

  describe(Gamma.toString) {
    describe("|- ? : String") {
      val tgt = Constructor("List", Constructor("String"))
      val results = Gamma.inhabit(tgt)
      it("should not be empty") {
        assert(results.nonEmpty)
      }
      it("should unroll exactly to Tree(map, Tree(f), Tree(l))") {
        assert(
          TreeGrammarEnumeration(results, tgt)
            .values
            .flatMap(_._2).toSet ==
            Set(Tree("map", Tree("f"), Tree("l")))
        )
      }
    }
  }

}