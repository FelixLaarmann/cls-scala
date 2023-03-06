package org.combinators.cls.examples

import org.combinators.cls.interpreter.{ReflectedRepository, combinator}
import org.combinators.cls.queries.BooleanQuery
import org.combinators.cls.types._
import org.combinators.cls.types.syntax._

object LabyrinthBenchmarkBFCL extends App {
  val labyrinthSize = 4
  val start: (Int, Int) = (0, 0)
  val goal: (Int, Int) = (labyrinthSize - 1, labyrinthSize - 1)

  def isFree(row: Int, col: Int): Boolean = {
    val seed = 0
    if (row == col) true else
      (BigInt(11).modPow((row + col + seed) * (row + col + seed) + col + 7, 1000003)) % BigInt(5) > 0
  }

  object SemanticTypes {
    def Free(posRow: Type, posCol: Type): Type =
      Constructor("Free", posRow, posCol)
    def Pos(row: Type, col: Type): Type = Constructor("Pos", row, col)
    def Seen(row: Type, col: Type): Type = Constructor("Seen_("+row.toString+", "+col.toString+")")
  }
  import SemanticTypes._

  def intToType(x: Int): Type = Constructor(x.toString)

  val freeFields: Map[String, Type] =
    (0 until labyrinthSize)
      .flatMap(row =>
        (0 until labyrinthSize).collect {
          case col if isFree(row, col) =>
            s"Pos_at_($row, $col)" -> Free(intToType(row), intToType(col))
        }
      )
      .toMap

  def move(drow_from: Int, dcol_from: Int, drow_to: Int, dcol_to: Int): Type = {
    val posFree = for {
      row <- 0 until labyrinthSize
      col <- 0 until labyrinthSize
    } yield Pos(intToType(row + drow_from), intToType(col + dcol_from)) =>: Free(intToType(row + drow_to), intToType(col + dcol_to)) =>: (Pos(intToType(row + drow_to), intToType(col + dcol_to)) :&: Seen(intToType(row + drow_to), intToType(col + dcol_to)))
    val seen = for {
      row <- 0 until labyrinthSize
      col <- 0 until labyrinthSize
    } yield Seen(intToType(row), intToType(col)) =>: Omega =>: Seen(intToType(row), intToType(col))
    Type.intersect(posFree ++ seen)
  }

  def singleMove(row:Int, col:Int, drow_from: Int, dcol_from: Int, drow_to: Int, dcol_to: Int): Type = {
    val posFree = Seq(Pos(intToType(row + drow_from), intToType(col + dcol_from)) =>: Free(intToType(row + drow_to), intToType(col + dcol_to)) =>: (Pos(intToType(row + drow_to), intToType(col + dcol_to)) :&: Seen(intToType(row + drow_to), intToType(col + dcol_to))))
    val seen = for {
      row2 <- 0 until labyrinthSize
      col2 <- 0 until labyrinthSize
    } yield Seen(intToType(row2), intToType(col2)) =>: Omega =>: Seen(intToType(row2), intToType(col2))
    Type.intersect(posFree ++ seen)
  }

  trait MovementRepository {
    @combinator object Start {
      def apply(): String = "Start" + start.toString()

      val semanticType: Type = Pos(intToType(start._1), intToType(start._2)) :&: Seen(intToType(start._1), intToType(start._2))
    }

    @combinator object Up {
      def apply(s1:String, s2:String): String = "Up("++s1++s2++")"

      val semanticType: Type = move(1, 0, 0, 0)
    }

    @combinator object Down {
      def apply(s1:String, s2:String): String = "Down("++s1++s2++")"

      val semanticType: Type =move(0, 0, 1, 0)
    }

    @combinator object Left {
      def apply(s1:String, s2:String): String = "Left("++s1++s2++")"

      val semanticType: Type = move(0, 1, 0, 0)
    }

    @combinator object Right {
      def apply(s1:String, s2:String): String = "Right("++s1++s2++")"

      val semanticType: Type = move(0, 0, 0, 1)
    }
  }

  trait SingleMovementRepository {
    @combinator object Start {
      def apply(): String = "Start" + start.toString()

      val semanticType: Type = Pos(intToType(start._1), intToType(start._2)) :&: Seen(intToType(start._1), intToType(start._2))
    }
  }

  case class PosAt(row: Int, col: Int) {
    def apply(): String = s"Pos_at_($row, $col)"

    val semanticType: Type = Free(intToType(row), intToType(col))
  }

  case class UpC(row: Int, col: Int){
    def apply(s1:String, s2:String): String = s"Up_($row, $col)("++s1++s2++")"

    val semanticType: Type = singleMove(row, col, 1, 0, 0, 0)
  }

  case class DownC(row: Int, col: Int) {
    def apply(s1:String, s2:String): String = s"Down_($row, $col)("++s1++s2++")"

    val semanticType: Type = singleMove(row, col, 0, 0, 1, 0)
  }

  case class LeftC(row: Int, col: Int) {
    def apply(s1:String, s2:String): String = s"Left_($row, $col)("++s1++s2++")"

    val semanticType: Type = singleMove(row, col, 0, 1, 0, 0)
  }

  case class RightC(row: Int, col: Int) {
    def apply(s1:String, s2:String): String = s"Right_($row, $col)("++s1++s2++")"

    val semanticType: Type = singleMove(row, col, 0, 0, 0, 1)
  }

  val tgt = Pos(intToType(goal._1), intToType(goal._2))
  println(s"|- ? : $tgt")

  lazy val GammaMovement = new MovementRepository {}

  val rowCol: Seq[(Int, Int)] = for {
    row <- 0 until labyrinthSize
    col <- 0 until labyrinthSize
  } yield (row, col)

  val reflectedMovementGamma = rowCol.foldLeft[ReflectedRepository[MovementRepository]](ReflectedRepository(GammaMovement, Taxonomy.empty , Kinding.empty))((rep, rc) => if (isFree(rc._1, rc._2)) rep.addCombinator(PosAt(rc._1, rc._2)) else rep)

  lazy val GammaSingleMovement = new SingleMovementRepository {}

  lazy val reflectedSingleMovementGamma = rowCol.foldLeft[ReflectedRepository[SingleMovementRepository]](ReflectedRepository(GammaSingleMovement, Taxonomy.empty, Kinding.empty))((rep, rc) => {
    lazy val repo = rep.addCombinator(UpC(rc._1, rc._2)).addCombinator(DownC(rc._1, rc._2)).addCombinator(LeftC(rc._1, rc._2)).addCombinator(RightC(rc._1, rc._2))
    if (isFree(rc._1, rc._2)) repo.addCombinator(PosAt(rc._1, rc._2)) else repo
  })
  def time[R](block: => R): R = {
    val t0 = System.nanoTime()
    val result = block // call-by-name
    val t1 = System.nanoTime()
    println("Elapsed time: " + (t1 - t0) / 1000000 + "ms")
    result
  }
  def test1(): Unit = time {
      val movementScripting = BooleanQuery[MovementRepository](reflectedMovementGamma)

      import movementScripting._
      import movementScripting.syntax._
      lazy val request: Formula = :?:(tgt) :/\: :~:(:?:(Seen(intToType(1), intToType(1))))

      lazy val movementInhabitationResult = movementScripting.Formula.eval[String](request)

      lazy val enumMovement = movementInhabitationResult.interpretedTerms

      println(enumMovement.index(0))
      println(enumMovement.index(1))
      println(enumMovement.index(2))
    }

  def test2(): Unit = time {
      val singleMovementScripting = BooleanQuery[SingleMovementRepository](reflectedSingleMovementGamma)


      import singleMovementScripting._
      import singleMovementScripting.syntax._

      lazy val request: Formula = :?:(tgt) :/\: (:~:(:?:(Seen(intToType(1), intToType(1)))))

      lazy val singleMovementInhabitationResult = singleMovementScripting.Formula.eval[String](request)

      lazy val enumSingleMovement = singleMovementInhabitationResult.interpretedTerms

      println(enumSingleMovement.index(0))
      println(enumSingleMovement.index(1))
      println(enumSingleMovement.index(2))
    }

  test1

  test2

}
