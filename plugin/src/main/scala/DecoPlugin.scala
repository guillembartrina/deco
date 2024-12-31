package deco.plugin

import dotty.tools.dotc.plugins.*
import dotty.tools.dotc.core.Contexts.*
import dotty.tools.dotc.core.Phases.*
import dotty.tools.dotc.cc.CheckCaptures
import dotty.tools.backend.sjs.GenSJSIR


var noCaptureChecking: Boolean = false
var compileScala2Library: Boolean = false
var debugInfo: Boolean = false

class DecoPlugin extends ResearchPlugin:
  def name: String = "deco"
  def description: String = "deco"

  override val optionsHelp: Option[String] =
    Some(
      "\t-P:deco:noCaptureChecking\t\tdo not use the capture checker, consider most methods and calls as suspendable\n"
      + "\t-P:deco:compileScala2Library\t\tcompile scala 2 standard library, with an special, less strict setup\n"
      + "\t-P:deco:debugInfo\t\tshow debug information\n"
    )


  override def init(options: List[String], plan: List[List[Phase]])(using Context): List[List[Phase]] =
    noCaptureChecking = options.exists(_ == "noCaptureChecking")
    compileScala2Library = options.exists(_ == "compileScala2Library")
    debugInfo = options.exists(_ == "debugInfo")

    val notCheckCaptures = (x: List[Phase]) => x.tail.nonEmpty || !x.head.isInstanceOf[CheckCaptures]
    val notGenSJSIR = (x: List[Phase]) => x.tail.nonEmpty || !x.head.isInstanceOf[GenSJSIR]
    val beforeCheckCaptures = plan.takeWhile(notCheckCaptures)
    val afterCheckCapturesToGenSJSIR = plan.dropWhile(notCheckCaptures).tail.takeWhile(notGenSJSIR)
    val fromGenSJSIR = plan.dropWhile(notGenSJSIR)

    val newPlan =
      beforeCheckCaptures
      ::: List(List(new CheckCapturesWrapperPhase))
      ::: afterCheckCapturesToGenSJSIR
      ::: List(List(new SegmentationPhase), List(new CallRedirectionPhase))
      ::: fromGenSJSIR

    newPlan
