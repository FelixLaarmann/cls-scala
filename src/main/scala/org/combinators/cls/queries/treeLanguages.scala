package org.combinators.cls.queries

import org.combinators.cls.inhabitation._
import org.combinators.cls.types.{Constructor, Omega, Type}


trait TreeGrammar {
  //our rules from CLS are always normalized
  val rules: Set[Rule]

  val startSymbol: Type //target

  lazy val nonTerminals : Set[Type] = rules.flatMap {
    case Failed(t) => Set(t)
    case Combinator(t, _) => Set(t)
    case Apply(t, f, a) => Set(t, f, a)
  }

  lazy val terminalNames : Set[String] = rules.foldLeft(Set.empty[String]){
    case (s, Combinator(_, name)) => s + name
    case (s, _) => s
  }

  def prettyPrint : String = {
    "TreeGrammar(\n  Startsymbol = " +
      startSymbol.toString + ",\n  " +
      nonTerminals.foldLeft("Nonterminals = {")((s,t) => s + t.toString + ", ") + "},\n" +
      terminalNames.foldLeft("Terminals = {")((s,n) => s + n + ", ") + "},\n" +
      "Rules = " + prettyPrintRuleSet(rules) + "\n)"
  }

  lazy val productiveNonTerminals : Set[Type] = {
    val prod1 : Set[Type] = rules.flatMap{
      case Combinator(t, _) => Set(t)
      case _ => Set.empty
    }
    var prod = prod1
    val appRules = rules.filter{
      case Apply(_,_,_) => true
      case _ => false
    }
    var nextProd = appRules.flatMap {
      case Apply(target, functionType, argumentType) => {
        if (prod.contains(functionType) && prod.contains(argumentType))
        {prod + target} else prod
      }
    }

    if (nextProd.isEmpty) {nextProd = prod}

    while (!prod.equals(nextProd)) {
      prod = nextProd
      nextProd = appRules.flatMap {
        case Apply(target, functionType, argumentType) =>
          if (prod.contains(functionType) && prod.contains(argumentType)) {
            prod + target
          } else {
            prod
          }
      }
    }
    prod
  }

  lazy val reachableNonTerminals : Set[Type] = {
    val reach0 : Set[Type] = Set(startSymbol)
    val appRules = rules.filter {
      case Apply(_, _, _) => true
      case _ => false
    }
    var reach: Set[Type] = reach0
    var nextReach = appRules.flatMap {
      case Apply(target, functionType, argumentType) =>
        if (reach.contains(target)) {
          reach + functionType + argumentType
        } else {
          reach
        }
    }

    if (nextReach.isEmpty) {nextReach = reach}

    while (!reach.equals(nextReach)) {
      reach = nextReach
      nextReach = appRules.flatMap {
        case Apply(target, functionType, argumentType) =>
          if (reach.contains(target)) {
            reach + functionType + argumentType
          } else {
            reach
          }
      }
    }
    reach
  }

  def productiveAndReachable(t : Type) : Boolean = productiveNonTerminals.contains(t) && reachableNonTerminals.contains(t)

  lazy val reduced : TreeGrammar = {
    val newRules = rules.filter {
      case Failed(target) => productiveAndReachable(target)
      case Combinator(target, _) => productiveAndReachable(target)
      case Apply(target, functionType, argumentType) => productiveAndReachable(target) &&
        this.productiveAndReachable(functionType) && productiveAndReachable(argumentType)
    }
    val newStart = startSymbol
    new TreeGrammar {
    override val rules: Set[Rule] = newRules
    override val startSymbol: Type = newStart
  }
  }

  //easy, since we only deal with normalized grammars
  lazy val topDownNFTA : TopDownNFTA = new TopDownNFTA {
    override val initialStates: Set[Type] = Set(startSymbol)
    override val transitions: Set[TopdownNFTAtransition] = rules.map {
      case Failed(target) => new TopdownNFTAtransition {
        override val symbol: Symbol = FailedS()
        override val fromState: Type = target
        override val targets: List[Type] = List.empty
      }
      case Combinator(target, combinator) => new TopdownNFTAtransition {
        override val symbol: Symbol = CombinatorS(combinator)
        override val fromState: Type = target
        override val targets: List[Type] = List.empty
      }
      case Apply(target, functionType, argumentType) => new TopdownNFTAtransition {
        override val symbol: Symbol = ApplyS()
        override val fromState: Type = target
        override val targets: List[Type] = List(functionType, argumentType)
      }
    }
  }
}

trait Symbol

final case class FailedS() extends Symbol

final case class CombinatorS(name : String) extends Symbol

final case class ApplyS() extends Symbol

trait Tree[V]{
  val symbol : Symbol
}

final case class FailedT[V]() extends Tree[V] {
  override val symbol: Symbol = FailedS()
}

final case class CombinatorT[V](name : String) extends Tree[V] {
  override val symbol: Symbol = CombinatorS(name)
}

final case class ApplyT[V](function : Tree[V], argument : Tree[V]) extends Tree[V] {
  override val symbol: Symbol = ApplyS()
}

final case class VariableT[V](x : V) extends Tree[V] {
  override val symbol: Symbol = FailedS()
}

object Tree{
  type Pos = List[Either[Unit,Unit]]

  def variables[V](tree: Tree[V]): List[V] = tree match {
    case ApplyT(function, argument) => variables(function) ++ variables(argument)
    case CombinatorT(_) => List.empty
    case FailedT() => List.empty
    case VariableT(x) => List(x)
  }

  def map[V,Q](tree: Tree[V], f: V => Q): Tree[Q] = tree match {
    case ApplyT(function, argument) => ApplyT(map(function, f), map(argument, f))
    case VariableT(x) => VariableT(f(x))
    case CombinatorT(n) => CombinatorT(n)
    case FailedT() => FailedT()
  }

  def positions[V](tree: Tree[V]): Set[Pos] = tree match {
    case ApplyT(function, argument) => (positions(function).map(ps => Left(()) +: ps) union positions(argument).map(ps => Right(()) +: ps)) + List.empty
    case _ => Set(List.empty)
  }

  def atPos[V](tree: Tree[V], pos: Pos) : Option[Either[Symbol, V]] = tree match {
    case ApplyT(function, argument) => pos match {
      case ::(Left(_), next) => atPos(function, next)
      case ::(Right(_), next) => atPos(argument, next)
      case Nil => Some(Left(ApplyS()))
    }
    case CombinatorT(name) => pos match {
      case ::(_, _) => None
      case Nil => Some(Left(CombinatorS(name)))
    }
    case FailedT() => pos match {
      case ::(_, _) => None
      case Nil => Some(Left(FailedS()))
    }
    case VariableT(x) => pos match {
      case ::(_, _) => None
      case Nil => Some(Right(x))
    }
  }
}

trait TopdownNFTAtransition {
  val symbol: Symbol
  val fromState: Type
  val targets: List[Type]
}

trait TopDownNFTA{

  val initialStates: Set[Type]

  val transitions: Set[TopdownNFTAtransition]

  lazy val states : Set[Type] = transitions.flatMap(t => t.targets.toSet + t.fromState)

  def prettyPrint: String = "Top-Down-NFTA(\n" +
    states.foldLeft("states = {")((s, q) => s + q.toString + ", ") + "},\n" +
    initialStates.foldLeft("initial states = {")((s, q) => s + q.toString + ", ") + "},\n" +
    prettyPrintTransitions(transitions)

  def prettyPrintTransitions[T](trans: Set[TopdownNFTAtransition]): String = trans.foldLeft("transitions = {")((s, t) => s +
    t.fromState.toString + " --> " + t.symbol.toString + t.targets.foldLeft("(")((s, q) => s + q.toString + ", ") + ")" + "; ") + "}"

  //applicable takes a tree and a state and checks recursively all applicable transitions, such that there is an
  //accepting run, if the result is non-empty.
  def applicable(tree : Tree[Type], state : Type) : Set[(TopdownNFTAtransition, List[TopdownNFTAtransition])] = tree match {
    case ApplyT(function, argument) =>
      val applicableTransitions = transitions.filter(t => (t.symbol == ApplyS()) && (t.fromState == state))
      for{
        trans <- applicableTransitions
        ts1 <- applicable(function, trans.targets.head)
        ts2 <- applicable(argument, trans.targets.tail.head)
      } yield (trans, List(ts1._1, ts2._1))
    case x =>
      transitions.filter(t => (t.symbol == x.symbol) && (t.fromState == state)).map((_,List.empty))
  }

  def accepts(tree : Tree[Type]) : Boolean = {
    val run = for {
      i <- initialStates
      (ts, _) <- applicable(tree, i)
    } yield ts
    run.nonEmpty
  }

  lazy val treeGrammar : TreeGrammar = {
    val newSymbol : Type = {
      val names = states.map(_.toString)
      var newName : String = "StartSymbol"
      while (names.contains(newName)) {
        newName = "New" + newName
      }
      Constructor(newName)
    }

    new TreeGrammar {
      override val rules: Set[Rule] = transitions.flatMap(t => t.symbol match {
        case ApplyS() =>
          val left = t.fromState
          if (initialStates.contains(left)) {
            Set(Apply(newSymbol, t.targets.head, t.targets.tail.head), Apply(left, t.targets.head, t.targets.tail.head))
          } else Set(Apply(left, t.targets.head, t.targets.tail.head))
        case CombinatorS(name) =>
          val left = t.fromState
          if (initialStates.contains(left)) {
            Set(Combinator(newSymbol, name), Combinator(left, name))
          } else Set(Combinator(left, name))
        case FailedS() =>
          val left = t.fromState
          if (initialStates.contains(left)) {
            Set(Failed(newSymbol), Failed(left))
          } else Set(Failed(left))
      })
      override val startSymbol: Type = newSymbol
    }
  }

  lazy val nfta : NFTA[Type] = {
    val bottomUpTransitions : Set[NFTAtransition[Type]] = transitions.map(tr => new NFTAtransition[Type] {
      override val symbol: Symbol = tr.symbol
      override val fromStates: List[Type] = tr.targets
      override val target: Type = tr.fromState
    })
    new NFTA[Type] {
      override val finalStates: Set[Type] = initialStates
      override val transitions: Set[NFTAtransition[Type]] = bottomUpTransitions
    }
  }
}

trait NFTAtransition[Q] {
  val symbol: Symbol
  val fromStates: List[Q]
  val target: Q

  def canEqual(obj: Any) = obj.isInstanceOf[NFTAtransition[Q]]

  override def equals(obj: Any): Boolean = obj match {
    case obj: NFTAtransition[Q] => obj.canEqual(this) &&
      obj.symbol == symbol &&
      obj.fromStates == fromStates &&
      obj.target == target
  }

  override def hashCode: Int = {
    val prime = 31
    var result = 1
    result = prime * result + symbol.hashCode()
    result = prime * result + (if (fromStates.isEmpty) 0 else fromStates.hashCode())
    result = prime * result + target.hashCode()
    result
  }
}

trait NFTA[Q]{
  val finalStates : Set[Q]

  val transitions : Set[NFTAtransition[Q]]

  lazy val states : Set[Q] = transitions.flatMap(t => t.fromStates.toSet + t.target)

  lazy val symbols : Set[Symbol] = transitions.map(_.symbol)

  def prettyPrint : String = "NFTA(\n" +
    states.foldLeft("states = {")((s, q) => s + q.toString + ", ") + "},\n" +
    finalStates.foldLeft("final states = {")((s, q) => s + q.toString + ", ") + "},\n" +
    prettyPrintTransitions(transitions)

  def prettyPrintTransitions[T](trans : Set[NFTAtransition[T]]) : String = trans.foldLeft("transitions = {")((s, t) => s + t.symbol.toString +
    t.fromStates.foldLeft("(")((s, q) => s + q.toString + ", ") + ") --> " + t.target.toString + "; ") + "}"

  def step(tree : Tree[Q]) : Set[Q] = tree match {
    case ApplyT(function, argument) =>
      val applicableTransitions = transitions.filter(_.symbol == ApplyS())
      val qs1 = step(function)
      val qs2 = step(argument)
      for{
        q1 <- qs1
        q2 <- qs2
        fittingDom = applicableTransitions.filter(_.fromStates == List(q1,q2))
        trans <- fittingDom
      } yield trans.target
    case x =>
      val applicableTransitions = transitions.filter(_.symbol == x.symbol)
      applicableTransitions.map(_.target)
  }

  def accepts(tree : Tree[Q]) : Boolean = step(tree).intersect(finalStates).nonEmpty


  def determinize: NFTA[Set[Q]] = {
    var q : Set[Set[Q]] = Set.empty
    var delta : Set[NFTAtransition[Set[Q]]] = Set.empty
    val transBySymbol = transitions.groupBy(_.symbol)
    val init : (Set[Set[Q]], Set[NFTAtransition[Set[Q]]]) = symbols.foldLeft((Set.empty[Set[Q]], Set.empty[NFTAtransition[Set[Q]]]))(
        (p, s) => {
          val qs: Set[Q] = transBySymbol(s).filter(_.fromStates.isEmpty).map(_.target)
          if (qs.nonEmpty) {
          (p._1 + qs, p._2 + new NFTAtransition[Set[Q]] {
            override val symbol: Symbol = s
            override val fromStates: List[Set[Q]] = List.empty
            override val target: Set[Q] = qs
          })
        } else {
            p
          }
        })
    var nextQ : Set[Set[Q]] = init._1
    var nextDelta : Set[NFTAtransition[Set[Q]]] = init._2
    while (!(delta == nextDelta)) {
      q = nextQ
      delta = nextDelta
      val trans : Set[NFTAtransition[Set[Q]]] = for {
        s <- symbols
        s1 <- q
        s2 <- q
        qsANDdoms = for {
          t <- transBySymbol(s)
          dom = t.fromStates
          if dom.nonEmpty
          if s1.contains(dom.head) && s2.contains(dom.tail.head)
        } yield (t.target, List(s1, s2))
        qs = qsANDdoms.map(_._1)
        dom <- qsANDdoms.map(_._2)
      } yield new NFTAtransition[Set[Q]] {

        override val symbol: Symbol = s
        override val fromStates: List[Set[Q]] = dom
        override val target: Set[Q] = qs
      }
      nextDelta = delta.union(trans)
      nextQ = q.union(trans.map(_.target))
      }
    val newF = nextQ.filter(s => s.intersect(finalStates).nonEmpty)
    new NFTA[Set[Q]] {
      override val finalStates: Set[Set[Q]] = newF
      override val transitions: Set[NFTAtransition[Set[Q]]] = delta
    }.reduce
    }

  def reduce : NFTA[Q] = {
    var marked : Set[Q] = Set.empty[Q]
    var nextMarked : Set[Q] = transitions.filter(_.fromStates.isEmpty).map(_.target)
    while (marked != nextMarked) {
      marked = nextMarked
      nextMarked = transitions.filter(_.fromStates.toSet.subsetOf(marked)).map(_.target)
    }
    val newFin = finalStates.intersect(marked)
    val newDelta = transitions.filter(t => marked.contains(t.target) && t.fromStates.toSet.subsetOf(marked))
    new NFTA[Q] {
      override val finalStates: Set[Q] = newFin
      override val transitions: Set[NFTAtransition[Q]] = newDelta
    }
  }

  def complete(f : Q => Type) : NFTA[Type] = {
    val dead  : Type = Omega //not Constructor("dead"), because a fresh name is required. But Omega is also ok...
    val newQ : Set[Type] = states.map(f) + dead
    val binArgs : Set[List[Type]] = for {
      q1 <- newQ
      q2 <- newQ
    } yield List(q1,q2)
    val newDelta = transitions.map(t => new NFTAtransition[Type] {
      override val symbol: Symbol = t.symbol
      override val fromStates: List[Type] = t.fromStates.map(f)
      override val target: Type = f(t.target)
    }).flatMap(t => if (t.fromStates.isEmpty) Set(t, new NFTAtransition[Type] {
      override val symbol: Symbol = t.symbol
      override val fromStates: List[Type] = List()
      override val target: Type = dead
    }) else binArgs.map(frSt => new NFTAtransition[Type] {
      override val symbol: Symbol = t.symbol
      override val fromStates: List[Type] = frSt
      override val target: Type = dead
    }) + t)
    val newFin = finalStates.map(f)
    new NFTA[Type] {
      override val finalStates: Set[Type] = newFin
      override val transitions: Set[NFTAtransition[Type]] = newDelta
    }
  }

  def completeWith(gamma : Repository)(f : Q => Type) : NFTA[Type] = {
    val newSymbols : Set[Symbol] = {
      val preNewSymbols : Set[Symbol] = gamma.keys.toSet.map(CombinatorS)
      preNewSymbols.--(symbols)
    }
    val dead: Type = Omega //not Constructor("dead"), because a fresh name is required. But Omega is also ok...
    val newQ: Set[Type] = Set(dead) ++ states.map(f)
    val binArgs: Set[List[Type]] = for {
        q1 <- newQ
        q2 <- newQ
      } yield List(q1, q2)
    val newTrans : Set[NFTAtransition[Type]] = newSymbols.map(s => new NFTAtransition[Type] {
      override val symbol: Symbol = s
      override val fromStates: List[Type] = List()
      override val target: Type = dead
    })
    val oldTrans : Set[NFTAtransition[Type]] = transitions.map(t => new NFTAtransition[Type] {
      override val symbol: Symbol = t.symbol
      override val fromStates: List[Type] = t.fromStates.map(f)
      override val target: Type = f(t.target)
    })
    val newDelta : Set[NFTAtransition[Type]] = {
      val binOldTrans: Set[NFTAtransition[Type]] = oldTrans.filter(t => t.symbol == ApplyS())
      val binTrans : Set[NFTAtransition[Type]] = {
        for {
          a <- binArgs.--(binOldTrans.map(_.fromStates))
        } yield new NFTAtransition[Type] {
          override val symbol: Symbol = ApplyS()
          override val fromStates: List[Type] = a
          override val target: Type = dead
        }
      }
      oldTrans union newTrans union binTrans
    }
    val newFin = finalStates.map(f)
    new NFTA[Type] {
      override val finalStates: Set[Type] = newFin
      override val transitions: Set[NFTAtransition[Type]] = newDelta
    }.reduce
  }

  def complement(f : Q => Type) : NFTA[Type] = {
    val completeDFTA : NFTA[Type] = this.determinize.complete(qs => Constructor(qs.foldLeft("")((s,q) => s + " ∪ " + q.toString)))
    new NFTA[Type] {
      override val finalStates: Set[Type] = completeDFTA.states.diff(completeDFTA.finalStates)
      override val transitions: Set[NFTAtransition[Type]] = completeDFTA.transitions
    }
  }

  def complementWith(gamma : Repository)(f : Q => Type) : NFTA[Type] = {
    val completeDFTA: NFTA[Type] = this.determinize.completeWith(gamma)(qs => Constructor(qs.foldLeft("")((s, q) => s + " ∪ " + q.toString)))
    new NFTA[Type] {
      override val finalStates: Set[Type] = completeDFTA.states.diff(completeDFTA.finalStates)
      override val transitions: Set[NFTAtransition[Type]] = completeDFTA.transitions
    }.reduce
  }

  def union(nfta : NFTA[Q])(f : Q => Type) : NFTA[Type] = {
    val leftDelta = transitions.map(t => new NFTAtransition[Type] {
      override val symbol: Symbol = t.symbol
      override val fromStates: List[Type] = t.fromStates.map(q => Constructor(f(q).toString ++ "_left"))
      override val target: Type = Constructor(f(t.target).toString ++ "_left")
    })
    val leftFin : Set[Type] = finalStates.map(x => Constructor(f(x).toString ++ "_left"))
    val rightDelta = nfta.transitions.map(t => new NFTAtransition[Type] {
      override val symbol: Symbol = t.symbol
      override val fromStates: List[Type] = t.fromStates.map(q => Constructor(f(q).toString ++ "_right"))
      override val target: Type = Constructor(f(t.target).toString ++ "_right")
    })
    val rightFin : Set[Type] = nfta.finalStates.map(x => Constructor(f(x).toString ++ "_right"))
    new NFTA[Type] {
      override val finalStates: Set[Type] = leftFin.union(rightFin)
      override val transitions: Set[NFTAtransition[Type]] = leftDelta.union(rightDelta)
    }.reduce
  }

  def intersection[H](nfta: NFTA[H]) : NFTA[(Q,H)] = {
    val newFin : Set[(Q, H)] = for {
      ql <- finalStates
      qr <- nfta.finalStates
    } yield (ql, qr)
    val newDelta : Set[NFTAtransition[(Q,H)]] = for {
      tl <- transitions
      tr <- nfta.transitions
      if tl.symbol == tr.symbol
      newSymbol = tl.symbol
    } yield new NFTAtransition[(Q,H)] {
      override val symbol: Symbol = newSymbol
      override val fromStates: List[(Q, H)] = tl.fromStates.zip(tr.fromStates)
      override val target: (Q, H) = (tl.target, tr.target)
    }
    new NFTA[(Q, H)] {
      override val finalStates: Set[(Q, H)] = newFin
      override val transitions: Set[NFTAtransition[(Q, H)]] = newDelta
    }.reduce
  }

  def topDownNFTA(f : Q => Type): TopDownNFTA = {
    val bottomUpTransitions: Set[TopdownNFTAtransition] = transitions.map(tr => new TopdownNFTAtransition {
      override val symbol: Symbol = tr.symbol
      override val fromState: Type = f(tr.target)
      override val targets: List[Type] = tr.fromStates.map(f)
    })
    new TopDownNFTA {
      override val initialStates: Set[Type] = finalStates.map(f)
      override val transitions: Set[TopdownNFTAtransition] = bottomUpTransitions
    }
  }
}

