package deco.plugin

import dotty.tools.dotc.plugins.*
import dotty.tools.dotc.config.Feature
import dotty.tools.dotc.core.Contexts.*
import dotty.tools.dotc.core.Names.*
import dotty.tools.dotc.core.Symbols.*
import dotty.tools.dotc.core.DenotTransformers.*
import dotty.tools.dotc.core.Types.*
import dotty.tools.dotc.core.Flags.*
import dotty.tools.dotc.ast.tpd.*
import dotty.tools.dotc.transform.*
import dotty.tools.dotc.util.*
import dotty.tools.dotc.report

import scala.annotation.tailrec


val suspendableLanes = collection.mutable.Set.empty[Symbol]

class SegmentationPhase extends PluginPhase with IdentityDenotTransformer:
  def phaseName: String = SegmentationPhase.name

  override def runsAfter: Set[String] = Set(RepeatableAnnotations.name)

  override def changesMembers: Boolean = true

  override def run(using Context): Unit =
    if !compileScala2Library && !noCaptureChecking && !Feature.ccEnabledSomewhere && !ctx.compilationUnit.needsCaptureChecking then
      report.error(s"enabling capture checking required in compilation unit ${ctx.compilationUnit.source.name}")
    super.run

  private val uniqueNamer: UniqueNamer = new UniqueNamer()

  private def fixSignatureClashes(zero: DefDef, others: List[DefDef])(using Context): (DefDef, List[DefDef]) =
    val enclosingClass = ctx.owner.asClass
    @tailrec def rec(zero: DefDef, othersPending: List[DefDef], othersDone: List[DefDef]): (DefDef, List[DefDef]) =
      if othersPending.isEmpty then
        (zero, othersDone)
      else
        val next = othersPending.last
        val symbol = next.symbol.asTerm

        if enclosingClass.info.decls.exists(sym => sym.name == symbol.name && sym.signature.clashes(symbol.signature)) then
          val newName = uniqueNamer.fresh(symbol.name.toString + "$d")
          val newSymbol = symbol.copy(name = symbol.name ++ newName.substring(newName.lastIndexOf("$d"))).asTerm
          val newNext = DefDef(newSymbol, paramss => next.rhs.changeOwner(symbol, newSymbol).subst(next.termParamss.flatMap(_.map(_.symbol)), paramss.flatMap(_.map(_.symbol))))
          val newZero = zero.subst(List(symbol), List(newSymbol))
          val newOthersPending = othersPending.init.map(other => other.subst(List(symbol), List(newSymbol)))
          rec(newZero, newOthersPending, newNext :: othersDone)
        else rec(zero, othersPending.init, next :: othersDone)
    rec(zero, others, Nil)

  // non-compiled suspendable functions
  override def transformDefDef(tree: DefDef)(using Context): Tree =
    val symbol = tree.symbol.asTerm
    if !symbol.isConstructor then
      if isSuspendable(symbol) then
        // single lane
        if debugInfo then println(s"segmenting ${symbol.fullName.show} -> single lane")
        val (zero, others) = fixSignatureClashes.tupled(segment(tree))
        zero.symbol.entered
        others.foreach(_.symbol.entered)
        laneInfo.single.update(symbol, zero.symbol.asTerm)
        suspendableLanes.add(zero.symbol)
        suspendableLanes.addAll(others.map(_.symbol))
        Thicket(zero :: others)
      else if mayBeSuspendable(symbol) || noCaptureCheckingBypass(symbol) then
        // dual lane
        if debugInfo then println(s"segmenting ${symbol.fullName.show} -> dual lane")
        val (zero, others) = fixSignatureClashes.tupled(segment(tree))
        zero.symbol.entered
        others.foreach(_.symbol.entered)
        laneInfo.dual.update(symbol, zero.symbol.asTerm)
        suspendableLanes.add(zero.symbol)
        suspendableLanes.addAll(others.map(_.symbol))
        Thicket(tree :: zero :: others)
      else
        tree
    else
      disallowSuspensionPointIn(tree.rhs)
      tree


object SegmentationPhase:
  val name: String = "segmentation"
