// normaliation-related logic

package deco.plugin

import dotty.tools.dotc.core.Contexts.*
import dotty.tools.dotc.core.Names.*
import dotty.tools.dotc.core.Symbols.*
import dotty.tools.dotc.ast.tpd.*
import dotty.tools.dotc.core.Types.*
import dotty.tools.dotc.core.Flags.*
import dotty.tools.dotc.core.NameKinds.UniqueNameKind
import dotty.tools.dotc.util.*


private val uniqueNames = Property.Key[UniqueNamer]

// generates a fresh mutable variable of given type and possibly initialized with given rhs, returns definition and reference trees
private def genFreshVar(tpe: Type, rhs: Option[Tree] = None)(using Context): (Tree, Tree) =
  val symbol = newSymbol(ctx.owner, termName(ctx.property(uniqueNames).get.fresh("$var")), Synthetic | Mutable, tpe).asTerm  // TODO: right owner, right nestingLevel ?
  (ValDef(symbol, rhs.getOrElse(defaultValue(tpe))), identFor(symbol))

// generates a fresh immutable variable of given type and initialized with given rhs, returns definition and reference trees
private def genFreshVal(tpe: Type, rhs: Tree)(using Context): (Tree, Tree) =
  val symbol = newSymbol(ctx.owner, termName(ctx.property(uniqueNames).get.fresh("$val")), Synthetic, tpe).asTerm  // TODO: right owner, right nestingLevel ?
  (ValDef(symbol, rhs), identFor(symbol))


// Normalize trees so that suspension points appear either in the right-hand side of a value definition or in tail position, and control operators are used as statements.
// TODO: optimization => decorate each subtree whether it contains a suspension point before normalizing

// normalizes given tree assuming it is in tail position
private def doNormalizeTail(tree: Tree)(using Context): Tree =
  require(hasSuspensionPoint(tree))
  tree match
    //case _: Ident => ???
    case _: SelectWithSig => ???
    case Select(qualifier, name) if hasSuspensionPoint(qualifier) =>
      val (qualifierStats, newQualifier) = doNormalize(qualifier)
      Block(qualifierStats, cpy.Select(tree)(qualifier = newQualifier, name = name))
    //case _: This => ???
    //case _: Super => ???
    case Apply(fun, args) if hasSuspensionPoint(fun) || args.exists(hasSuspensionPoint) =>
      val (funStats, newFun) =
        if hasSuspensionPoint(fun)
        then doNormalize(fun)
        else (Nil, fun)
      val (argsStatss, newArgs) =
        args.map(arg =>
          if hasSuspensionPoint(arg)
          then doNormalize(arg)
          else (Nil, arg)
        ).unzip
      Block(funStats ++ argsStatss.flatten, cpy.Apply(tree)(fun = newFun, args = newArgs))
    case TypeApply(fun, args) if hasSuspensionPoint(fun) =>
      val (funStats, newFun) = doNormalize(fun)
      Block(funStats, cpy.TypeApply(tree)(fun = newFun, args = args))
    //case _: Literal => ???
    case _: New => ???
    case Typed(expr, tpt) if hasSuspensionPoint(expr) =>
      val (exprStats, newExpr) = doNormalize(expr)
      Block(exprStats, cpy.Typed(tree)(expr = newExpr, tpt = tpt))
    case _: NamedArg => ???
    case Assign(lhs, rhs) if hasSuspensionPoint(lhs) || hasSuspensionPoint(rhs) =>
      val (lhsStats, newLhs) =
        if hasSuspensionPoint(lhs)
        then doNormalize(lhs)
        else (Nil, lhs)
      val (rhsStats, newRhs) =
        if hasSuspensionPoint(rhs)
        then doNormalize(rhs)
        else (Nil, rhs)
      Block(lhsStats ++ rhsStats, cpy.Assign(tree)(lhs = newLhs, rhs = newRhs))
    case Block(stats, expr) if stats.exists(hasSuspensionPoint) || hasSuspensionPoint(expr) =>
      val newStatss =
        stats.map(stat =>
          if hasSuspensionPoint(stat)
          then
            stat match
              case valDef @ ValDef(name, tpt, _) =>
                val (rhsStats, newRhs) = doNormalize(valDef.rhs)
                rhsStats.map(_.changeOwner(valDef.symbol, ctx.owner)) :+ cpy.ValDef(valDef)(name = name, tpt = tpt, rhs = newRhs)
              case stat =>
                val (statStats, newStat) = doNormalize(stat)
                statStats :+ newStat
          else List(stat)
        )
      val newExpr =
        if hasSuspensionPoint(expr)
        then doNormalizeTail(expr)
        else expr
      cpy.Block(tree)(stats = newStatss.flatten, expr = newExpr)
    case If(cond, thenp, elsep) if hasSuspensionPoint(cond) || hasSuspensionPoint(thenp) || hasSuspensionPoint(elsep) =>
      val newThenp =
        if hasSuspensionPoint(thenp)
        then doNormalizeTail(thenp)
        else thenp
      val newElsep =
        if hasSuspensionPoint(elsep)
        then doNormalizeTail(elsep)
        else elsep
      if hasSuspensionPoint(cond)
      then
        val (condStats, newCond) = doNormalize(cond)
        Block(condStats, cpy.If(tree)(cond = newCond, thenp = newThenp, elsep = newElsep))
      else cpy.If(tree)(cond = cond, thenp = newThenp, elsep = newElsep)
    case _: InlineIf => ???
    case _: Closure => ???
    case _: InlineMatch => ???
    case Match(selector, cases) =>  // patterns are integer or string constants
      // selector is always a reference to a local, cases always end with return --> no need to doNormalize
      val newCases =
        cases.map(kase =>
          if hasSuspensionPoint(kase.body)
          then cpy.CaseDef(kase)(pat = kase.pat, guard = kase.guard, body = doNormalizeTail(kase.body))
          else kase
        )
      cpy.Match(tree)(selector = selector, cases = newCases)
    case _: CaseDef => ???
    case Labeled(bind, expr) if hasSuspensionPoint(expr) =>
      // paths always end with return (?) --> no need to doNormalize
      cpy.Labeled(tree)(bind = bind, expr = doNormalizeTail(expr))
    case Return(expr, from) if hasSuspensionPoint(expr) =>
      val (exprStats, newExpr) = doNormalize(expr)
      Block(exprStats, cpy.Return(tree)(expr = newExpr, from = from))
    case WhileDo(cond, body) if hasSuspensionPoint(cond) || hasSuspensionPoint(body) =>
      val newBody =
        if hasSuspensionPoint(body)
        then
          val (bodyStats, newBody) = doNormalize(body)
          Block(bodyStats, newBody)
        else body
      if hasSuspensionPoint(cond)
      then
        val (condStats, newCond) = doNormalize(cond)
        val (condStatsInner, newCondInner) = doNormalize(cond)
        val (varStat, condVar) = genFreshVar(defn.BooleanType, Some(newCond))
        Block(condStats :+ varStat, cpy.WhileDo(tree)(cond = condVar, body = Block(newBody +: condStatsInner, Assign(condVar, newCondInner))))
      else cpy.WhileDo(tree)(cond = cond, body = newBody) 
    case Try(expr, cases, finalizer) if hasSuspensionPoint(expr) || cases.exists(kase => hasSuspensionPoint(kase.body)) =>
      val newExpr =
        if hasSuspensionPoint(expr)
        then doNormalizeTail(expr)
        else expr
      val newCases =
        cases.map(kase =>
          if hasSuspensionPoint(kase.body)
          then cpy.CaseDef(kase)(pat = kase.pat, guard = kase.guard, body = doNormalizeTail(kase.body))
          else kase
        )
      disallowSuspensionPointIn(finalizer)
      cpy.Try(tree)(expr = newExpr, cases = newCases, finalizer = finalizer)
    case SeqLiteral(elems, elemtpt) if elems.exists(hasSuspensionPoint) =>
      val (elemsStatss, newElems) =
        elems.map(elem =>
          if hasSuspensionPoint(elem)
          then doNormalize(elem)
          else (Nil, elem)
        ).unzip
      Block(elemsStatss.flatten, cpy.SeqLiteral(tree)(elems = newElems, elemtpt = elemtpt))
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
      // the tree itself is the only suspension point
      tree

private inline def liftIfSuspension(tree: Tree, stats: List[Tree], expr: Tree)(using Context): (List[Tree], Tree) =
  if isSuspensionPoint(tree) then
    if tree.tpe.isRef(defn.UnitClass) then
      (stats :+ expr, unitLiteral)
    else
      val (valStat, treeVal) = genFreshVal(tree.tpe, expr)
      (stats :+ valStat, treeVal)
  else (stats, expr)

// normalizes given tree assuming it is in non-tail position, returns the sequence of trees that make up the normalization and the reference tree
private def doNormalize(tree: Tree)(using Context): (List[Tree], Tree) =
  require(hasSuspensionPoint(tree))
  tree match
    //case _: Ident => ???
    case _: SelectWithSig => ???
    case Select(qualifier, name) if hasSuspensionPoint(qualifier) =>
      val (qualifierStats, newQualifier) = doNormalize(qualifier)
      liftIfSuspension(tree, qualifierStats, cpy.Select(tree)(qualifier = newQualifier, name = name))
    //case _: This => ???
    //case _: Super => ???
    case Apply(fun, args) if hasSuspensionPoint(fun) || args.exists(hasSuspensionPoint) =>
      val (funStats, newFun) =
        if hasSuspensionPoint(fun)
        then doNormalize(fun)
        else (Nil, fun)
      val (argsStatss, newArgs) =
        args.map(arg =>
          if hasSuspensionPoint(arg)
          then doNormalize(arg)
          else (Nil, arg)
        ).unzip
      liftIfSuspension(tree, funStats ++ argsStatss.flatten, cpy.Apply(tree)(fun = newFun, args = newArgs))
    case TypeApply(fun, args) if hasSuspensionPoint(fun) =>
      val (funStats, newFun) = doNormalize(fun)
      liftIfSuspension(tree, funStats, cpy.TypeApply(tree)(fun = newFun, args = args))
    //case _: Literal => ???
    case _: New => ???
    case Typed(expr, tpt) if hasSuspensionPoint(expr) =>
      val (exprStats, newExpr) = doNormalize(expr)
      liftIfSuspension(tree, exprStats, cpy.Typed(tree)(expr = newExpr, tpt = tpt))
    case _: NamedArg => ???
    case Assign(lhs, rhs) if hasSuspensionPoint(lhs) || hasSuspensionPoint(rhs) =>
      val (lhsStats, newLhs) =
        if hasSuspensionPoint(lhs)
        then doNormalize(lhs)
        else (Nil, lhs)
      val (rhsStats, newRhs) =
        if hasSuspensionPoint(rhs)
        then doNormalize(rhs)
        else (Nil, rhs)
      liftIfSuspension(tree, lhsStats ++ rhsStats, cpy.Assign(tree)(lhs = newLhs, rhs = newRhs))
    case Block(stats, expr) if stats.exists(hasSuspensionPoint) || hasSuspensionPoint(expr) =>
      if tree.tpe.isRef(defn.UnitClass) || tree.tpe.isRef(defn.NothingClass) then
        val newStatss =
          stats.map(stat =>
            if hasSuspensionPoint(stat)
            then
              stat match
                case valDef @ ValDef(name, tpt, _) =>
                  val (rhsStats, newRhs) = doNormalize(valDef.rhs)
                  rhsStats.map(_.changeOwner(valDef.symbol, ctx.owner)) :+ cpy.ValDef(valDef)(name = name, tpt = tpt, rhs = newRhs)
                case stat =>
                  val (statStats, newStat) = doNormalize(stat)
                  statStats :+ newStat
            else List(stat)
          )
        val (exprStats, newExpr) =
          if hasSuspensionPoint(expr)
          then doNormalize(expr)
          else (Nil, expr)
        (List(cpy.Block(tree)(stats = newStatss.flatten ++ exprStats, newExpr)), unitLiteral)
      else
        val (varStat, blockVar) = genFreshVar(tree.tpe)
        val newStatss =
          stats.map(stat =>
            if hasSuspensionPoint(stat)
            then
              stat match
                case valDef @ ValDef(name, tpt, _) =>
                  val (rhsStats, newRhs) = doNormalize(valDef.rhs)
                  rhsStats.map(_.changeOwner(valDef.symbol, ctx.owner)) :+ cpy.ValDef(valDef)(name = name, tpt = tpt, rhs = newRhs)
                case stat =>
                  val (statStats, newStat) = doNormalize(stat)
                  statStats :+ newStat
            else List(stat)
          )
        val (exprStats, newExpr) =
          if hasSuspensionPoint(expr)
          then doNormalize(expr)
          else (Nil, expr)
        (List(varStat, cpy.Block(tree)(stats = newStatss.flatten ++ exprStats, Assign(blockVar, newExpr))), blockVar)
    case _: InlineIf => ???
    case If(cond, thenp, elsep) if hasSuspensionPoint(cond) || hasSuspensionPoint(thenp) || hasSuspensionPoint(elsep) =>
      if tree.tpe.isRef(defn.UnitClass) || tree.tpe.isRef(defn.NothingClass) then
        val (condStats, newCond) =
          if hasSuspensionPoint(cond)
          then doNormalize(cond)
          else (Nil, cond)
        val newThenp =
          if hasSuspensionPoint(thenp)
          then
            val (thenpStats, newThenp) = doNormalize(thenp)
            Block(thenpStats, newThenp)
          else thenp
        val newElsep =
          if hasSuspensionPoint(elsep)
          then
            val (elsepStats, newElsep) = doNormalize(elsep)
            Block(elsepStats, newElsep)
          else elsep
        (condStats :+ cpy.If(tree)(cond = newCond, thenp = newThenp, elsep = newElsep), unitLiteral)
      else
        val (varStat, ifVar) = genFreshVar(tree.tpe)
        val (condStats, newCond) =
          if hasSuspensionPoint(cond)
          then doNormalize(cond)
          else (Nil, cond)
        val newThenp =
          if hasSuspensionPoint(thenp)
          then
            val (thenpStats, newThenp) = doNormalize(thenp)
            Block(thenpStats, Assign(ifVar, newThenp))
          else Assign(ifVar, thenp)
        val newElsep =
          if hasSuspensionPoint(elsep)
          then
            val (elsepStats, newElsep) = doNormalize(elsep)
            Block(elsepStats, Assign(ifVar, newElsep))
          else Assign(ifVar, elsep)
        (varStat +: condStats :+ cpy.If(tree)(cond = newCond, thenp = newThenp, elsep = newElsep), ifVar)
    case _: Closure => ???
    case _: InlineMatch => ???
    case _: Match => ???  // always ocurrs in tail position of a labeled  
    case _: CaseDef => ???
    case Labeled(bind, expr) if hasSuspensionPoint(expr) =>
      // paths always end with return (?) --> no need to doNormalize
      if tree.tpe.isRef(defn.UnitClass) || tree.tpe.isRef(defn.NothingClass) then
        val newExpr = doNormalizeTail(expr)
        (List(cpy.Labeled(tree)(bind = bind, expr = newExpr)), unitLiteral)
      else
        assert(bind.body.isEmpty)

        val newBindSymbol = bind.symbol.copy(info = defn.UnitType).asTerm
        val newBind = Bind(newBindSymbol, EmptyTree)
        val newFrom = identFor(newBindSymbol)

        val (varStat, labeledVar) = genFreshVar(tree.tpe)
        val newExpr = doNormalizeTail(expr)

        // wrap sequence of trees in a block, if needed
        inline def singleize(trees: List[Tree]): Tree =
          assert(trees.nonEmpty)
          if trees.tail.nonEmpty
          then Block(trees.init, trees.last)
          else trees.last

        // transform return statements to the target label into an assignment of the return value to the labeled variable followed by returning Unit
        def patchReturns(tree: Tree): List[Tree] = tree match
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
          case Return(expr, from) if bind.symbol == from.symbol =>
            List(Assign(labeledVar, expr), cpy.Return(tree)(expr = unitLiteral, from = newFrom))
          case Block(stats, expr) =>
            val newStatss = stats.map(patchReturns)
            val newExpr = patchReturns(expr)
            List(cpy.Block(tree)(stats = newStatss.flatten ++ newExpr.init, expr = newExpr.last))
          case _: InlineIf => ???
          case If(cond, thenp, elsep) =>
            val newCond = patchReturns(cond)
            val newThenp = patchReturns(thenp)
            val newElsep = patchReturns(elsep)
            newCond.init :+ cpy.If(tree)(newCond.last, singleize(newThenp), singleize(newElsep))
          case _: Closure => ???
          case _: InlineMatch => ???
          case Match(selector, cases) =>
            val newCases = cases.map(kase =>
              val newBody = patchReturns(kase.body)
              cpy.CaseDef(kase)(pat = kase.pat, guard = kase.guard, singleize(newBody))
            )
            List(cpy.Match(tree)(selector = selector, cases = newCases))
          case _: CaseDef => ???
          case Labeled(bind, expr) =>
            val newExpr = patchReturns(expr)
            List(cpy.Labeled(tree)(bind = bind, expr = singleize(newExpr)))
          case WhileDo(cond, body) =>
            val newCond = patchReturns(cond)
            val newBody = patchReturns(body)
            newCond.init :+ cpy.WhileDo(tree)(cond = newCond.last, body = singleize(newBody))
          case Try(expr, cases, finalizer) =>
            val newExpr = patchReturns(expr)
            val newCases = cases.map(kase =>
              val newBody = patchReturns(kase.body)
              cpy.CaseDef(kase)(pat = kase.pat, guard = kase.guard, singleize(newBody))
            )
            List(cpy.Try(tree)(expr = singleize(newExpr), cases = newCases, finalizer = finalizer))
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
          //case _: ValDef => ???
          case _: DefDef => ???
          case _: TypeDef => ???
          case _: Template => ???
          case _: Import => ???
          case _: Export => ???
          case _: PackageDef => ???
          //case _: Annotated => ???
          //case _: Thicket => ???
          case tree =>
            List(tree)
      
        val finalExpr = singleize(patchReturns(newExpr))
        (List(varStat, cpy.Labeled(tree)(bind = newBind, expr = finalExpr)), labeledVar)
    case Return(expr, from) if hasSuspensionPoint(expr) =>  // mmm
      val (exprStats, newExpr) = doNormalize(expr)
      (exprStats, cpy.Return(tree)(expr = newExpr, from = from))
    case WhileDo(cond, body) if hasSuspensionPoint(cond) || hasSuspensionPoint(body) =>
      val newBody =
        if hasSuspensionPoint(body)
        then
          val (bodyStats, newBody) = doNormalize(body)
          Block(bodyStats, newBody)
        else body
      if hasSuspensionPoint(cond)
      then
        val (condStats, newCond) = doNormalize(cond)
        val (condStatsInner, newCondInner) = doNormalize(cond)
        val (varStat, condVar) = genFreshVar(defn.BooleanType, Some(newCond))
        (condStats :+ varStat :+ cpy.WhileDo(tree)(cond = cond, body = Block(newBody +: condStatsInner, Assign(condVar, newCondInner))), unitLiteral)
      else (List(cpy.WhileDo(tree)(cond = cond, body = newBody)), unitLiteral)
    case Try(expr, cases, finalizer) if hasSuspensionPoint(expr) || cases.exists(kase => hasSuspensionPoint(kase.body)) || hasSuspensionPoint(finalizer) =>
      if tree.tpe.isRef(defn.UnitClass) || tree.tpe.isRef(defn.NothingClass) then
        val newExpr =
          if hasSuspensionPoint(expr)
          then
            val (exprStats, newExpr) = doNormalize(expr)
            Block(exprStats, newExpr)
          else expr
        val newCases =
          cases.map(kase =>
            if hasSuspensionPoint(kase.body)
            then
              val (bodyStats, newBody) = doNormalize(kase.body)
              cpy.CaseDef(kase)(pat = kase.pat, guard = kase.guard, body = Block(bodyStats, newBody))
            else cpy.CaseDef(kase)(pat = kase.pat, guard = kase.guard, body = kase.body)
          )
        disallowSuspensionPointIn(finalizer)
        (List(cpy.Try(tree)(expr = newExpr, cases = newCases, finalizer = finalizer)), unitLiteral)
      else
        val (varStat, tryVar) = genFreshVar(tree.tpe)
        val newExpr =
          if hasSuspensionPoint(expr)
          then
            val (exprStats, newExpr) = doNormalize(expr)
            Block(exprStats, Assign(tryVar, newExpr))
          else Assign(tryVar, expr)
        val newCases =
          cases.map(kase =>
            if hasSuspensionPoint(kase.body)
            then
              val (bodyStats, newBody) = doNormalize(kase.body)
              cpy.CaseDef(kase)(pat = kase.pat, guard = kase.guard, body = Block(bodyStats, Assign(tryVar, newBody)))
            else cpy.CaseDef(kase)(pat = kase.pat, guard = kase.guard, body = Assign(tryVar, kase.body))
          )
        (List(varStat, cpy.Try(tree)(expr = newExpr, cases = newCases, finalizer = finalizer)), tryVar)
    case SeqLiteral(elems, elemtpt) if elems.exists(hasSuspensionPoint) =>
      val (elemsStatss, newElems) =
        elems.map(elem =>
          if hasSuspensionPoint(elem)
          then doNormalize(elem)
          else (Nil, elem)
        ).unzip
      liftIfSuspension(tree, elemsStatss.flatten, cpy.SeqLiteral(tree)(elems = newElems, elemtpt = elemtpt))
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
      // the tree itself is the only suspension point
      if tree.tpe.isRef(defn.UnitClass) then
        (List(tree), unitLiteral)
      else
        val (valStat, treeVal) = genFreshVal(tree.tpe, tree)
        (List(valStat), treeVal)


// normalizes the given tree
def normalize(tree: Tree)(using Context): Tree =
  require(hasSuspensionPoint(tree))
  doNormalizeTail(tree)(using ctx.withProperty(uniqueNames, Some(new UniqueNamer())))
