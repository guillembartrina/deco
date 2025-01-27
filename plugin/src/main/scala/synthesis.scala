// synthesis-related logic

package deco.plugin

import dotty.tools.dotc.core.Contexts.*
import dotty.tools.dotc.core.Names.*
import dotty.tools.dotc.core.NameKinds.*
import dotty.tools.dotc.core.Symbols.*
import dotty.tools.dotc.core.Types.*
import dotty.tools.dotc.core.Flags.*
import dotty.tools.dotc.ast.tpd.*


// given a suspendable method, returns the instrumented method and the associated segments
// note: the segments must be 'entered'
def segment(defDef: DefDef)(using Context): (DefDef, List[DefDef]) =
  require(isSuspendable(defDef.symbol.asTerm) || mayBeSuspendable(defDef.symbol.asTerm) || noCaptureCheckingBypass(defDef.symbol.asTerm))

  val symbol = defDef.symbol.asTerm
  val rhs = defDef.rhs
  val newName = SuspendableName(symbol.name)
  val newUniqueNames = new UniqueNameKind(newName.toString + '$')
  val newSymbol = symbol.copy(name = newName).asTerm

  val newCtx = ctx.withOwner(symbol)

  if rhs.isEmpty then
    // abstract definition
    (DefDef(newSymbol, EmptyTree), List.empty[DefDef])
  else if !hasSuspensionPoint(rhs)(using newCtx) then
    // does not contain suspension point, but one cannot possibly know this from the mere interface during separate compilation, so we must create the lane
    (DefDef(newSymbol, paramss => rhs.changeOwner(symbol, newSymbol).subst(defDef.termParamss.flatMap(_.map(_.symbol)), paramss.flatMap(_.map(_.symbol)))), List.empty[DefDef])
  else
    // normalize the body
    val normalizedRhs = normalize(rhs)(using newCtx)

    // build the associated cfg
    val rhsCfg = cfgize(normalizedRhs)(using newCtx)

    // compute the entrypoints
    val entrypoints = computeEntrypoints(rhsCfg)(using newCtx)

    if entrypoints.isEmpty
    then
      // the suspension is in tail position, no segmentation is needed, we still rename it tho
      (DefDef(newSymbol, paramss => normalizedRhs.changeOwner(symbol, newSymbol).subst(defDef.termParamss.flatMap(_.map(_.symbol)), paramss.flatMap(_.map(_.symbol)))), List.empty[DefDef])
    else
      // create the symbols for the segments and compute auxiliar information on locals
      val entrypointInfo = entrypoints.zipWithIndex.map((e, i) =>
        val locals = e.result.fold(e.locals)(r => e.locals - r).toList

        val (valLocals, varLocals) = locals.partition(l => !l.is(Mutable))

        val varLocalsArgs = varLocals.map(l => l.copy(name = l.name ++ "$arg", flags = l.flags &~ Mutable).asTerm)

        val args = valLocals ::: varLocalsArgs
        
        // convert Unit to BoxedUnit, because of lambda/closure issues
        val resultType = if symbol.info.resultType.isRef(defn.UnitClass) then defn.BoxedUnitClass.typeRef else symbol.info.resultType
        val newInfo = MethodType(args.map(_.name), args.map(_.info), resultType)
        val newSymbol = symbol.copy(name = newUniqueNames.fresh(), flags = symbol.flags | Private | Synthetic, info = newInfo).asTerm
        (newSymbol, args, valLocals ::: varLocals, varLocals.zip(varLocalsArgs))
      )

      val entrypointMap = entrypoints.zip(entrypointInfo).map((e, ei) => (e.entry, (ei._1, ei._3))).toMap

      // emit the bodies of the segments and build the segments
      val segmentation = entrypoints.zip(entrypointInfo).map((e, i) =>
        val newNewCtx = newCtx.withOwner(i._1)
        val segment = emitSegment(e.entry, e.result, entrypointMap)(using newNewCtx)
        val newRhs =
          if i._4.isEmpty
          then segment
          else
            val vars = i._4.map((v, a) => ValDef(v, identFor(a)))
            Block(vars, segment)

        val boxUnitReturns = new TreeMap:
          override def transform(tree: Tree)(using Context): Tree = tree match
            case Return(expr, from) if from.symbol == symbol => Return(ref(defn.BoxedUnit_UNIT), from)
            case _ => super.transform(tree)

        // do we need to substitute the Return::from symbol to newSymbol?

        val finalRhs =
          if i._1.info.resultType.isRef(defn.BoxedUnitClass)
          then Block(List(boxUnitReturns.transform(newRhs)), ref(defn.BoxedUnit_UNIT))
          else newRhs
        DefDef(i._1, paramss => finalRhs.changeOwner(symbol, i._1).subst(i._2, paramss.flatMap(_.map(_.symbol))))
      )

      val zeroSegment = emitSegment(rhsCfg.root, None, entrypointMap)(using newCtx)
      val zero = DefDef(newSymbol, paramss => zeroSegment.changeOwner(symbol, newSymbol).subst(defDef.termParamss.flatMap(_.map(_.symbol)), paramss.flatMap(_.map(_.symbol))))
    
      (zero, segmentation)
