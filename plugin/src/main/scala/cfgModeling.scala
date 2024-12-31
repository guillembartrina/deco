// cfg-modeling-related logic

package deco.plugin

import scala.compiletime.uninitialized

import dotty.tools.dotc.core.Constants.*
import dotty.tools.dotc.core.Contexts.*
import dotty.tools.dotc.core.Names.*
import dotty.tools.dotc.core.Symbols.*
import dotty.tools.dotc.ast.tpd.*
import dotty.tools.dotc.core.Types.*
import dotty.tools.dotc.core.Flags.*


// Model normalizes trees as a CFG, that we can analyze to extract information and emit the segments from it.

// base representation of a node in the cfg
sealed trait Node:
  var successor: Option[Node] = None

object Node:

  // sequence of non-suspending trees
  class Thicket(val trees: List[Tree]) extends Node

  // suspension in local initialization
  class Local(val local: ValDef) extends Node

  // suspension in tail or statement position
  class Expr(val tree: Tree) extends Node

  // marker for the start of a block
  class BlockStart extends Node:
    var body: Node = uninitialized
    var end: BlockEnd = uninitialized

  // marker for the end of a block
  class BlockEnd extends Node

  // if statement
  class IfStart(val cond: Tree) extends Node:
    var thenp: Node = uninitialized
    var elsep: Node = uninitialized
    var end: IfEnd = uninitialized
  
  // marker for the end of an if statement
  class IfEnd extends Node

  // while statement
  class WhileStart(val cond: Tree) extends Node:
    var body: Node = uninitialized
    var end: WhileEnd = uninitialized
  
  // marker for the end of a while statement
  class WhileEnd extends Node:
    var start: WhileStart = uninitialized

  // try statement
  class TryStart(val casesPatGuard: List[(Tree, Tree)], val finalizer: Tree) extends Node:
    var expr: Node = uninitialized
    var casesBody: List[Node] = uninitialized
    var middle: TryMiddle = uninitialized
    var end: TryEnd = uninitialized
  
  // special marker for the end of the expr of a try statement
  class TryMiddle extends Node:
    var end: TryEnd = uninitialized
    var start: TryStart = uninitialized
  
  // marker for the end of a try statement
  class TryEnd extends Node

  // labeled statement
  class LabeledStart(val bind: Bind) extends Node:
    var expr: Node = uninitialized
    var end: LabeledEnd = uninitialized
  
  // marker for the end of a labeled statement
  class LabeledEnd extends Node:
    var start: LabeledStart = uninitialized

  // match statement
  class MatchStart(val selector: Tree, val casesPat: List[Tree]) extends Node:
    var casesBody: List[Node] = uninitialized
    var end: MatchEnd = uninitialized

  // special marker for the end of a match statement
  class MatchEnd extends Node

// representation of a cfg: start and end nodes
opaque type Cfg = (Node, Node)

extension (cfg: Cfg)
  def root: Node = cfg._1


// --- ANALYSIS ---

// returns whether the given node is in tail position
private def isTail(node: Node)(using Context): Boolean =
  import Node.*

  def killsTailness(node: Node): Boolean = node match
    case _: Thicket => true
    case _: Local => true
    case _: Expr => true
    case _: BlockStart => true
    //case _: BlockEnd => ???
    case _: IfStart => true
    //case _: IfEnd => ???
    case _: WhileStart => true
    //case _: WhileEnd => ???
    case _: TryStart => true
    //case tm: TryMiddle => ???
    //case _: TryEnd => ???
    case _: LabeledStart => true
    //case _: LabeledEnd => ???
    case _: MatchStart => true
    //case _: MatchEnd => ???
    case _ => false

  node match
    //case t: Thicket => ???
    case l: Local =>
      // skip tail unbox operations
      l.successor match
        case Some(t: Thicket) =>
          t.successor.map(succ => isTail(succ) && !killsTailness(succ)).getOrElse(true)
          && (
            t.trees match
              case List(Apply(fun, List(i: Ident))) => isUnbox(fun.symbol) && i.symbol == l.local.symbol
              case _ => false
          )
        case _ => false
    //case e: Expr => ???
    case bs: BlockStart => isTail(bs.end)
    //case _: BlockEnd => ???
    case is: IfStart => isTail(is.end)
    //case _: IfEnd => ???
    case ws: WhileStart => isTail(ws.end)
    //case _: WhileEnd => ???
    case ts: TryStart => isTail(ts.end)
    case tm: TryMiddle => isTail(tm.end)
    //case _: TryEnd => ???
    case ls: LabeledStart => isTail(ls.end)
    //case _: LabeledEnd => ???
    case ms: MatchStart => isTail(ms.end)
    //case _: MatchEnd => ???
    case other =>
      other.successor.map(succ => isTail(succ) && !killsTailness(succ)).getOrElse(true)

// returns the set of symbols of the free identifiers ocurring in the sub-tree starting from the given node
private def freeLocals(node: Node)(using Context): Set[TermSymbol] =
  import Node.*
  val seen = collection.mutable.Set[Node]()
  inline def optionRec(succ: Option[Node]): Set[TermSymbol] = succ.map(rec).getOrElse(Set.empty[TermSymbol])
  def rec(node: Node): Set[TermSymbol] = node match
    case t: Thicket =>
      t.trees.foldRight(optionRec(t.successor))((tree, acc) =>
        tree match
          case valDef: ValDef => (acc - valDef.symbol.asTerm) ++ idents(valDef.rhs)
          case _ => acc ++ idents(tree)
      )
    case l: Local =>
      (optionRec(l.successor) - l.local.symbol.asTerm) ++ idents(l.local.rhs)
    case e: Expr =>
      optionRec(e.successor) ++ idents(e.tree)
    case bs: BlockStart =>
      seen.addOne(bs.end)
      val body = rec(bs.body)
      optionRec(bs.end.successor) ++ body
    case be: BlockEnd =>
      if !seen.contains(be)
      then optionRec(be.successor)
      else Set.empty[TermSymbol]
    case is: IfStart =>
      seen.addOne(is.end)
      val thenp = rec(is.thenp)
      val elsep = rec(is.elsep)
      optionRec(is.end.successor) ++ idents(is.cond) ++ thenp ++ elsep
    case ie: IfEnd =>
      if !seen.contains(ie)
      then optionRec(ie.successor)
      else Set.empty[TermSymbol]
    case ws: WhileStart =>
      seen.addOne(ws.end)
      val body = rec(ws.body)
      optionRec(ws.end.successor) ++ idents(ws.cond) ++ body
    case we: WhileEnd =>
      // we may find re-declarations of already seen locals in the while body, but is not an issue
      if !seen.contains(we)
      then rec(we.start)
      else Set.empty[TermSymbol]
    case ts: TryStart =>
      seen.addOne(ts.middle)
      seen.addOne(ts.end)
      val expr = rec(ts.expr)
      val casess = ts.casesPatGuard.zip(ts.casesBody).map((patGuard, body) => (idents(patGuard._2) ++ rec(body)) -- patVars(patGuard._1).map(_.asTerm))
      optionRec(ts.end.successor) ++ expr ++ casess.flatten ++ idents(ts.finalizer)
    case tm: TryMiddle =>
      if !seen.contains(tm)
      then
        val ts = tm.start
        seen.addOne(ts.end)
        val casess = ts.casesPatGuard.zip(ts.casesBody).map((patGuard, body) => (idents(patGuard._2) ++ rec(body)) -- patVars(patGuard._1).map(_.asTerm))
        optionRec(tm.end.successor) ++ casess.flatten ++ idents(ts.finalizer)
      else Set.empty[TermSymbol]
    case te: TryEnd =>
      if !seen.contains(te)
      then optionRec(te.successor)
      else Set.empty[TermSymbol]
    case ls: LabeledStart =>
      seen.addOne(ls.end)
      val expr = rec(ls.expr)
      optionRec(ls.end.successor) ++ expr
    case le: LabeledEnd =>
      if !seen.contains(le)
      then optionRec(le.successor)
      else Set.empty[TermSymbol]
    case ms: MatchStart =>
      seen.addOne(ms.end)
      val casess = ms.casesBody.map(rec)
      optionRec(ms.end.successor) ++ casess.flatten
    case me: MatchEnd =>
      if !seen.contains(me)
      then optionRec(me.successor)
      else Set.empty[TermSymbol]
  rec(node)

// representation of an entrypoint: starting node, optional symbol of the (immutable) variable initialized with the result of the suspension, set of symbols of the free identifiers ocurring in the segment
case class Entrypoint(entry: Node, result: Option[TermSymbol], locals: Set[TermSymbol])

// computes the list of entrypoints for the given cfg
def computeEntrypoints(cfg: Cfg)(using Context): List[Entrypoint] =
  import Node.*
  val seen = collection.mutable.Set[Node]()
  inline def optionRec(succ: Option[Node]): List[Entrypoint] = succ.map(rec).getOrElse(List.empty[Entrypoint])
  def rec(node: Node): List[Entrypoint] = node match
    case t: Thicket =>
      optionRec(t.successor)
    case l: Local =>
      l.successor.filterNot(_ => isTail(l)).map(succ =>
        Entrypoint(succ, Some(l.local.symbol.asTerm), freeLocals(succ)) :: rec(succ) 
      ).getOrElse(List.empty[Entrypoint])
    case e: Expr =>
      e.successor.filterNot(_ => isTail(e)).map(succ =>
        Entrypoint(succ, None, freeLocals(succ)) :: rec(succ)
      ).getOrElse(List.empty[Entrypoint])
    case bs: BlockStart =>
      seen.addOne(bs.end)
      val body = rec(bs.body)
      body ::: optionRec(bs.end.successor)
    case _: BlockEnd => List.empty[Entrypoint] // ???
    case is: IfStart =>
      seen.addOne(is.end)
      val thenp = rec(is.thenp)
      val elsep = rec(is.elsep)
      thenp ::: elsep ::: optionRec(is.end.successor)
    case _: IfEnd => List.empty[Entrypoint] // ???
    case ws: WhileStart =>
      seen.addOne(ws.end)
      val body = rec(ws.body)
      body ::: optionRec(ws.end.successor)
    case _: WhileEnd => List.empty[Entrypoint] // ???
    case ts: TryStart =>
      seen.addOne(ts.middle)
      seen.addOne(ts.end)
      val expr = rec(ts.expr)
      val casess = ts.casesBody.map(rec)
      expr ::: casess.flatten ::: optionRec(ts.end.successor)
    case _: TryMiddle => List.empty[Entrypoint] // ???
    case _: TryEnd => List.empty[Entrypoint] // ???
    case ls: LabeledStart =>
      seen.addOne(ls.end)
      val expr = rec(ls.expr)
      expr ::: optionRec(ls.end.successor)
    case _: LabeledEnd => List.empty[Entrypoint] // ???
    case ms: MatchStart =>
      seen.addOne(ms.end)
      val casess = ms.casesBody.map(rec)
      casess.flatten ::: optionRec(ms.end.successor)
    case _: MatchEnd => List.empty[Entrypoint] // ???
  rec(cfg._1)


// --- CONVERSION ---

// returns the cfg corresponding to the given tree
// note: the given tree is normalized, hence suspension points are on the rhs of a local or ocurr in statement or tail position
def cfgize(tree: Tree)(using Context): Cfg =
  require(hasSuspensionPoint(tree))
  tree match
    //case _: Ident => ???
    //case _: Select => ???
    case _: SelectWithSig => ???
    //case _: This => ???
    //case _: Super => ???
    //case _: Apply => ???
    //case _: TypeApply => ???
    //case _: Literal => ???
    case _: New => ???
    //case _: Typed => ???
    case _: NamedArg => ???
    //case _: Assign => ???
    case Block(stats, expr) =>
      val blockStart = new Node.BlockStart()
      val blockEnd = new Node.BlockEnd()
      blockStart.end = blockEnd
      val (exprFirst, exprLast) =
        if hasSuspensionPoint(expr)
        then cfgize(expr)
        else
          val exprFirstLast = new Node.Thicket(List(expr))
          (exprFirstLast, exprFirstLast)
      exprLast.successor = Some(blockEnd)
      def tryExtendThicket(tree: Tree, last: Node): Node =
        last match
          case t: Node.Thicket =>
            val treeFirstLast = new Node.Thicket(tree :: t.trees)
            treeFirstLast.successor = last.successor
            treeFirstLast
          case _ =>
            val treeFirstLast = new Node.Thicket(List(tree))
            treeFirstLast.successor = Some(last)
            treeFirstLast
      val first = stats.foldRight(exprFirst)((stat, last) =>
        stat match
          case valDef: ValDef =>
            if isSuspensionPoint(valDef.rhs)
            then
              val statFirstLast = new Node.Local(valDef)
              statFirstLast.successor = Some(last)
              statFirstLast
            else
              tryExtendThicket(stat, last)
          case _ =>
            if hasSuspensionPoint(stat)
            then
              val (statFirst, statLast) = cfgize(stat)
              statLast.successor = Some(last)
              statFirst
            else
              tryExtendThicket(stat, last)
      )
      blockStart.body = first
      (blockStart, blockEnd)
    case _: InlineIf => ???
    case If(cond, thenp, elsep) =>
      val ifStart = new Node.IfStart(cond)
      val ifEnd = new Node.IfEnd()
      ifStart.end = ifEnd
      val (thenpFirst, thenpLast) =
        if hasSuspensionPoint(thenp)
        then cfgize(thenp)
        else
          val exprFirstLast = new Node.Thicket(List(thenp))
          (exprFirstLast, exprFirstLast)
      ifStart.thenp = thenpFirst
      thenpLast.successor = Some(ifEnd)
      val (elsepFirst, elsepLast) =
        if hasSuspensionPoint(elsep)
        then cfgize(elsep)
        else
          val exprFirstLast = new Node.Thicket(List(elsep))
          (exprFirstLast, exprFirstLast)
      ifStart.elsep = elsepFirst
      elsepLast.successor = Some(ifEnd)
      (ifStart, ifEnd)
    case _: Closure => ???
    case _: InlineMatch => ???
    case Match(selector, cases) =>
      val matchStart = new Node.MatchStart(selector, cases.map(_.pat))
      val matchEnd = new Node.MatchEnd()
      matchStart.end = matchEnd
      val casesBody = cases.map(kase =>
        val (bodyFirst, bodyLast) =
          if hasSuspensionPoint(kase.body)
          then cfgize(kase.body)
          else
            val bodyFirstLast = new Node.Thicket(List(kase.body))
            (bodyFirstLast, bodyFirstLast)
        bodyLast.successor = Some(matchEnd)
        bodyFirst
      )
      matchStart.casesBody = casesBody
      (matchStart, matchEnd)
    case _: CaseDef => ???
    case Labeled(bind, expr) =>
      val labeledStart = new Node.LabeledStart(bind)
      val labeledEnd = new Node.LabeledEnd()
      labeledStart.end = labeledEnd
      labeledEnd.start = labeledStart
      val (exprFirst, exprLast) = cfgize(expr)
      labeledStart.expr = exprFirst
      exprLast.successor = Some(labeledEnd)
      (labeledStart, labeledEnd)
    //case _: Return => ???
    case WhileDo(cond, body) =>
      val whileStart = new Node.WhileStart(cond)
      val whileEnd = new Node.WhileEnd()
      whileStart.end = whileEnd
      whileEnd.start = whileStart
      val (bodyFirst, bodyLast) = cfgize(body)
      whileStart.body = bodyFirst
      bodyLast.successor = Some(whileEnd)
      (whileStart, whileEnd)
    case Try(expr, cases, finalizer) =>
      val tryStart = new Node.TryStart(cases.map(kase => (kase.pat, kase.guard)), finalizer)
      val tryMiddle = new Node.TryMiddle()
      val tryEnd = new Node.TryEnd()
      tryStart.middle = tryMiddle
      tryStart.end = tryEnd
      tryMiddle.start = tryStart
      tryMiddle.end = tryEnd
      val (exprFirst, exprLast) =
        if hasSuspensionPoint(expr)
        then cfgize(expr)
        else
          val exprFirstLast = new Node.Thicket(List(expr))
          (exprFirstLast, exprFirstLast)
      tryStart.expr = exprFirst
      exprLast.successor = Some(tryMiddle)
      val casesBody = cases.map(kase =>
        val (bodyFirst, bodyLast) =
          if hasSuspensionPoint(kase.body)
          then cfgize(kase.body)
          else
            val bodyFirstLast = new Node.Thicket(List(kase.body))
            (bodyFirstLast, bodyFirstLast)
        bodyLast.successor = Some(tryEnd)
        bodyFirst
      )
      tryStart.casesBody = casesBody
      (tryStart, tryEnd)
    //case _: SeqLiteral => ???
    case _: JavaSeqLiteral => ???  // TODO?
    case _: Inlined => ???
    case _: Quote => ???
    case _: Splice => ???
    case _: QuotePattern => ???
    case _: SplicePattern => ???
    case _: Hole => ???
    // type trees
    case _: SingletonTypeTree => ???
    case _: RefinedTypeTree => ???
    case _: AppliedTypeTree => ???
    case _: LambdaTypeTree => ???
    case _: TermLambdaTypeTree => ???
    case _: MatchTypeTree => ???
    case _: ByNameTypeTree => ???
    case _: TypeBoundsTree => ???
    // pattern trees
    case _: Bind => ???
    case _: Alternative => ???
    case _: UnApply => ???
    case _: ValDef => ???
    case _: DefDef => ???
    case _: TypeDef => ???
    case _: Template => ???
    case _: Import => ???
    case _: Export => ???
    case _: PackageDef => ???
    //case _: Annotated => ???
    case _: Thicket => ???
    case tree =>
      val treeFirstLast = new Node.Expr(tree)
      (treeFirstLast, treeFirstLast)


private inline def returnDefault(using Context): Return =
  if ctx.owner.info.resultType.isRef(defn.UnitClass) then
    Return(unitLiteral, ctx.owner)
  else if ctx.owner.info.resultType.isRef(defn.BoxedUnitClass) then
    Return(ref(defn.BoxedUnit_UNIT), ctx.owner)
  else
    Return(defaultValue(ctx.owner.info.resultType), ctx.owner)


// given starting node, the optional symbol of the (immutable) variable initialized with the result of the suspension and information about all the entrypoints,
// traverses the cfg while building the target segment
// - if 'result' is defined, injects the (immutable) variable initialized with the result from the suspension at the very begining  
// - injects the suspending guard and the push of the corresponding following frame at each entrypoint
def emitSegment(node: Node, result: Option[TermSymbol], entrypoints: Map[Node, (TermSymbol, List[TermSymbol])])(using Context): Tree =
  import Node.*
  var layer: List[Tree] = Nil
  
  // result of suspension point is always assigned to an immutable variable
  result.foreach(res => layer = ValDef(res, resultAs(res.info)) :: layer)

  var first = true
  val seen = collection.mutable.Set[Node]()

  // wrap sequence of trees in a block, if needed
  inline def singleizeReverse(trees: List[Tree]): List[Tree] =
    if trees.isEmpty then
      Nil
    else if trees.tail.isEmpty then
      trees.head :: Nil
    else
    Block(trees.tail.reverse, trees.head) :: Nil

  def rec(node: Node): Unit =
    if !first && entrypoints.contains(node)
    then
      val ei = entrypoints(node)
      val guard = If(
        suspending,
        Block(List(pushLiftedClosure(Closure(ei._2.map(identFor), identFor(ei._1), EmptyTree)), returnDefault), unitLiteral),
        unitLiteral
      )
      layer = guard :: layer
    first = false

    node match
      case t: Thicket =>
        /// val newTrees =
        ///   if isTail(t) && t.trees.last.tpe.isRef(defn.UnitClass)
        ///   then t.trees :+ ref(defn.BoxedUnit_UNIT)
        ///   else t.trees
        layer = t.trees.reverse ::: layer
        t.successor.foreach(rec)
      case l: Local =>
        layer = l.local :: layer
        l.successor.foreach(rec)
      case e: Expr =>
        layer = e.tree :: layer
        e.successor.foreach(rec)
      case bs: BlockStart =>
        val prevlayer = layer
        layer = Nil
        seen.addOne(bs.end)
        rec(bs.body)
        layer = Block(layer.tail.reverse, layer.head) :: prevlayer
        bs.end.successor.foreach(rec)
      case be: BlockEnd =>
        if !seen.contains(be)
        then
          layer = singleizeReverse(layer)
          be.successor.foreach(rec)
      case is: IfStart =>
        val prevlayer = layer
        layer = Nil
        seen.addOne(is.end)
        rec(is.thenp)
        val thenp = layer.head
        layer = Nil
        rec(is.elsep)
        layer = If(is.cond, thenp, layer.head) :: prevlayer
        is.end.successor.foreach(rec)
      case ie: IfEnd =>
        if !seen.contains(ie)
        then
          layer = singleizeReverse(layer)
          ie.successor.foreach(rec)
      case ws: WhileStart =>
        val prevlayer = layer
        layer = Nil
        seen.addOne(ws.end)
        rec(ws.body)
        layer = WhileDo(ws.cond, layer.head) :: prevlayer
        ws.end.successor.foreach(rec)
      case we: WhileEnd =>
        if !seen.contains(we)
        then
          layer = singleizeReverse(layer)
          rec(we.start)
      case ts: TryStart =>
        val prevlayer = layer
        layer = Nil
        seen.addOne(ts.middle)
        seen.addOne(ts.end)
        rec(ts.expr)
        val expr = layer.head
        layer = Nil
        val cases = ts.casesPatGuard.zip(ts.casesBody).map((patGuard, body) =>
          rec(body)
          val body2 = layer.head
          layer = Nil
          CaseDef(patGuard._1, patGuard._2, body2)
        )
        layer = Try(expr, cases, ts.finalizer) :: prevlayer
        ts.end.successor.foreach(rec)
      case tm: TryMiddle =>
        if !seen.contains(tm)
        then
          singleizeReverse(layer).headOption.foreach(expr =>
            layer = Nil
            val ts = tm.start
            seen.addOne(ts.end)
            val cases = ts.casesPatGuard.zip(ts.casesBody).map((patGuard, body) =>
              rec(body)
              val body2 = layer.head
              layer = Nil
              CaseDef(patGuard._1, patGuard._2, body2)
            )
            layer = Try(expr, cases, ts.finalizer) :: Nil
          )          
          tm.end.successor.foreach(rec)
      case te: TryEnd =>
        if !seen.contains(te)
        then
          layer = singleizeReverse(layer)
          te.successor.foreach(rec)
      case ls: LabeledStart =>
        val prevlayer = layer
        layer = Nil
        seen.addOne(ls.end)
        rec(ls.expr)
        layer = Labeled(ls.bind, layer.head) :: prevlayer
        ls.end.successor.foreach(rec)
      case le: LabeledEnd =>
        if !seen.contains(le)
        then
          singleizeReverse(layer).headOption.foreach(expr =>
            layer = Nil
            val ls = le.start
            layer = Labeled(ls.bind, expr) :: Nil
          )          
          le.successor.foreach(rec)
      case ms: MatchStart =>
        val prevlayer = layer
        layer = Nil
        seen.addOne(ms.end)
        val cases = ms.casesPat.zip(ms.casesBody).map((pat, body) =>
          rec(body)
          val body2 = layer.head
          layer = Nil
          CaseDef(pat, EmptyTree, body2)
        )
        layer = Match(ms.selector, cases) :: prevlayer
        ms.end.successor.foreach(rec)
      case me: MatchEnd =>
        if !seen.contains(me)
        then
          layer = singleizeReverse(layer)
          me.successor.foreach(rec)
  rec(node)
  layer.head


// --- DEBUG ---

def printNode(node: Node)(using Context): String =
  import Node.*
  node match
    case t: Thicket => s"<\n${t.trees.map(_.show).mkString("\n")}\n>\n"
    case l: Local => s"loc ${l.local.show}}\n"
    case e: Expr => s"exp ${e.tree.show}}\n"
    case bs: BlockStart => "{\n"
    case be: BlockEnd => "}\n"
    case is: IfStart => s"if ${is.cond.show}\n"
    case ie: IfEnd => "endif\n"
    case ws: WhileStart => s"while ${ws.cond.show}\n"
    case we: WhileEnd => "endwhile\n"
    case ts: TryStart => "try\n"
    case tm: TryMiddle => "catch\n"
    case te: TryEnd => "endtry\n"
    case ls: LabeledStart => s"label[${ls.bind.name}]\n"
    case le: LabeledEnd => "endlabel\n"
    case ms: MatchStart => s"${ms.selector.show} match\n"
    case me: MatchEnd => "endmatch\n"
  
def prettyPrint(cfg: Cfg)(using Context): String =
  import Node.*
  val builder = new StringBuilder()
  var count = 0
  val seen = collection.mutable.Map[Node, Int]()
  def rec(node: Node, prefix: String): Unit =
    if seen.contains(node)
    then builder.append(s"$prefix|-> label ${seen(node)}\n")
    else
      seen(node) = count
      builder.append(s"$prefix| $count: ${printNode(node)}")
      count += 1
      node match
        //case _: Thicket => ???
        //case _: Local => ???
        //case _: Expr => ???
        case bs: BlockStart =>
          rec(bs.body, prefix)
        //case _: BlockEnd => ???
        case is: IfStart =>
          rec(is.elsep, prefix + "| ")
          rec(is.thenp, prefix)
        //case _: IfEnd => ???
        case ws: WhileStart =>
          rec(ws.body, prefix)
        //case _: WhileEnd => ???
        case ts: TryStart =>
          ts.casesBody.map(body => rec(body, prefix + "|C "))
          rec(ts.expr, prefix)
        case tm: TryMiddle =>
          rec(tm.end, prefix)
        //case _: TryEnd => ???
        case ls: LabeledStart =>
          rec(ls.expr, prefix)
        //case _: LabeledEnd => ???
        case ms: MatchStart =>
          ms.casesBody.zipWithIndex.map((body, i) => rec(body, prefix + "| " * i))
        //case _: MatchEnd => ???
        case _ =>
          node.successor.foreach(succ => rec(succ, prefix))
  rec(cfg._1, "")
  builder.toString
