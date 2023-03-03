package org.combinators.cls.queries

import org.combinators.cls.inhabitation
import org.combinators.cls.interpreter.{InhabitationResult, ReflectedRepository}
import org.combinators.cls.types.{Constructor, Omega, Type}
case class BooleanQuery[R](gamma : ReflectedRepository[R]) {

  trait Formula

  final case class Union(left: Formula, right: Formula) extends Formula

  final case class Intersection(left: Formula, right: Formula) extends Formula

  final case class Negation(formula: Formula) extends Formula

  final case class Inhabit(request: Type) extends Formula

  object Formula {

    val repository: ReflectedRepository[R] = gamma

    def eval[nativeType](f : Formula)(implicit targetTag: scala.reflect.runtime.universe.WeakTypeTag[nativeType]) : InhabitationResult[nativeType] = fromGrammar[nativeType](evalGrammar[nativeType](f))

    private def evalGrammar[nativeType](f: Formula)(implicit targetTag: scala.reflect.runtime.universe.WeakTypeTag[nativeType]): TreeGrammar = f match {
      case Inhabit(request) => toGrammar[nativeType](gamma.inhabit[nativeType](request))
      case Intersection(left, right) => intersection(evalGrammar[nativeType](left), evalGrammar[nativeType](right))
      case Negation(formula) => intersection(negation(evalGrammar[nativeType](formula)), toGrammar[nativeType](gamma.inhabit[nativeType](Omega))) //negation(evalGrammar[nativeType](formula))
      case Union(left, right) => union(evalGrammar[nativeType](left), evalGrammar[nativeType](right))
    }

    private def toGrammar[nativeType](iR: InhabitationResult[nativeType]): TreeGrammar = new TreeGrammar {
      override val rules: Set[inhabitation.Rule] = iR.rules
      override val startSymbol: Type = iR.target
    }

    private def fromGrammar[nativeType](grammar: TreeGrammar)(implicit targetTag: scala.reflect.runtime.universe.WeakTypeTag[nativeType]): InhabitationResult[nativeType] = new InhabitationResult[nativeType](grammar.rules, grammar.startSymbol, gamma.evalInhabitant[nativeType])

    private def intersection(left: TreeGrammar, right: TreeGrammar): TreeGrammar = {
      val l = left.topDownNFTA.nfta
      val r = right.topDownNFTA.nfta
      val inter: NFTA[(Type, Type)] = l.intersection(r)
      inter.topDownNFTA(p => Constructor(p._1.toString ++ "x" ++ p._2.toString)).treeGrammar.reduced
    }

    private def union(left: TreeGrammar, right: TreeGrammar): TreeGrammar = {
      val l = left.topDownNFTA.nfta
      val r = right.topDownNFTA.nfta
      val u = l.union(r)(x => x)
      u.topDownNFTA(x => x).treeGrammar.reduced
    }

    private def negation(g : TreeGrammar): TreeGrammar = {
      val nfta = g.topDownNFTA.nfta
      val complement = nfta.complementWith(gamma.combinators)(x => x)
      complement.topDownNFTA(x => x).treeGrammar.reduced
    }
  }

  trait FormulaSyntax {

    /** The formula constructed so far. */
    val formula: Formula

    /** The intersection of `ty` and `other`  */
    def :&&:(other: Formula): Formula =
      Intersection(other, formula)

    /** The union of `ty` and `other` */
    def :||:(other: Formula): Formula =
      Union(formula, other)
/*
    /** The complement of `ty` */
    def <!>(): Formula =
      Negation(formula)


 */
  }


  trait ToFormulaSyntax {
    implicit def toFormulaSyntax(fromF: Formula): FormulaSyntax =
      new FormulaSyntax {
        lazy val formula: Formula = fromF
      }
  }

  object syntax extends ToFormulaSyntax {
    def :!!:(formula : Formula): Formula =
      Negation(formula)

    def :?:(request : Type): Formula =
      Inhabit(request)
  }


}