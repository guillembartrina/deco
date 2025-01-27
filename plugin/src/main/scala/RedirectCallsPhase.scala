package deco.plugin

import dotty.tools.dotc.plugins.*
import dotty.tools.dotc.core.Contexts.*
import dotty.tools.dotc.core.Names.*
import dotty.tools.dotc.core.Symbols.*
import dotty.tools.dotc.core.Types.*
import dotty.tools.dotc.core.Flags.*
import dotty.tools.dotc.core.DenotTransformers.*
import dotty.tools.dotc.ast.tpd.*
import dotty.tools.dotc.transform.*
import dotty.tools.dotc.util.*


class CallRedirectionPhase extends PluginPhase with IdentityDenotTransformer:
  def phaseName: String = CallRedirectionPhase.name

  override def runsAfter: Set[String] = Set(SegmentationPhase.name)

  // within regular method -->
  // - redirect closures to the associated suspendable single lane. they must necessarily be the lambda of a top-level introducer.
  private val regularMethod = new TreeMap:
    override def transform(tree: Tree)(using Context): Tree = tree match
      case apply @ Apply(fun, _) =>
        val symbol = fun.symbol
        // sanity check
        assert(!laneInfo.single.contains(symbol))
        super.transform(tree)
      case Closure(_, meth, _) =>
        val symbol = meth.symbol.asTerm
        if laneInfo.single.contains(symbol) then
          tree.subst(List(symbol), List(laneInfo.single(symbol)))
        else if laneInfo.dual.contains(symbol) then
          tree.subst(List(symbol), List(laneInfo.dual(symbol)))
          // may happen with wrappers around boundaries
        else
          // sanity check
          assert(!symbol.isDefinedInBinary)
          tree
      case _ => super.transform(tree)

  // within suspendable method -->
  // - redirect calls to the associated suspendable single lane
  // - redirect calls to dual lane function that may suspend to the associated suspendable second lane 
  // - redirect calls to compiled functions that may suspend to the associated suspendable lane, assuming existence and crafting the symbol
  // - redirect closures to the associated suspendable single lane
  // - redirect closures to the associated suspendable second lane
  private def suspendableMethod(bridge: Boolean) = new TreeMap:
    override def transform(tree: Tree)(using Context): Tree = tree match
      case apply @ Apply(fun, _) if fun.symbol.isTerm =>
        val symbol = fun.symbol.asTerm
        if laneInfo.single.contains(symbol) then
          // single lane
          super.transform(tree).subst(List(symbol), List(laneInfo.single(symbol)))
        else if laneInfo.dual.contains(symbol) && (callMaySuspend(apply) || bridge || noCaptureCheckingBypass(symbol)) then
          // dual lane
          super.transform(tree).subst(List(symbol), List(laneInfo.dual(symbol)))
        else if symbol != library.boundary_apply && (callMaySuspend(apply) || noCaptureCheckingBypass(symbol))
          && (!compileScala2Library || (!symbol.isDefinedInSource && !symbol.is(JavaDefined))) then
          assert(!symbol.isDefinedInSource || noCaptureCheckingBypass(symbol))
          // call to compiled suspendable function --> craft symbol
          val zero = symbol.copy(name = SuspendableName(symbol.name)).asTerm
          super.transform(tree).subst(List(symbol), List(zero))
        else
          super.transform(tree)
      case Closure(_, meth, _) =>
        val symbol = meth.symbol.asTerm
        if laneInfo.single.contains(symbol) then
          // single lane
          tree.subst(List(symbol), List(laneInfo.single(symbol)))
        else if laneInfo.dual.contains(symbol) then
          // dual lane
          tree.subst(List(symbol), List(laneInfo.dual(symbol)))
        else
          // sanity check
          //assert(!symbol.isDefinedInBinary)
          tree
      case _ => super.transform(tree)

  
  override def transformDefDef(tree: DefDef)(using Context): Tree =
    val symbol = tree.symbol.asTerm
    if suspendableLanes.contains(symbol) || symbol.is(Bridge) then
      // suspendable function
      cpy.DefDef(tree)(rhs = suspendableMethod(symbol.is(Bridge)).transform(tree.rhs))
    else
      // regular function
      cpy.DefDef(tree)(rhs = regularMethod.transform(tree.rhs))


object CallRedirectionPhase:
  val name: String = "callRedirection"
