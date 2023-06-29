// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.gobra.ast.internal.transform

import viper.gobra.ast.{internal => in}
import viper.gobra.reporting.Source
//import viper.gobra.reporting.Source.SlicingExpressionAnnotation
import viper.gobra.reporting.Source.Parser.Single
import viper.gobra.util.Violation.violation
import scala.util.Random

/**
  * Transformation responsible for generating call-graph edges from interface methods to their implementations' methods.
  * This is necessary to soundly verify termination in the presence of dynamic method binding.
  */
object SyntacticCheck extends InternalTransform {
  override def name(): String = "syntactic_check_for_slices"
   val random= new Random()
   var methodsToAdd: Set[in.Member] = Set.empty
  var methodsToRemove: Set[in.Member]= Set.empty
   var definedFunctionsDelta: Map[in.FunctionProxy, in.FunctionLikeMember] = Map.empty 

  /**
    * Program-to-program transformation
    */
  override def transform(p: in.Program): in.Program = p match {
    case in.Program(_, members, _) =>

      def checkBody(m: in.Member): Unit = m match {
        case m: in.Function =>{m.Annotation.setslices(random.nextInt(2));
         val proxy= in.FunctionProxy(m.name.name + "$" + m.Annotation.slices)(m.info)
          var function = in.Function(proxy,m.args,m.results,m.pres,m.posts,m.terminationMeasures, m.body)(m.info);
          function.Annotation.setslices(m.Annotation.slices);
         
          methodsToRemove += m; methodsToAdd += function ; definedFunctionsDelta+= proxy -> function
        
        
        
        }
       
        case _ =>
      }

      /*
      Checks the expressions for subslicing expressions
       */
      def checkExpr(e: in.Expr): Boolean = {
        var slice = false
        e.visit {
          case elem: in.Slice => slice = true
          case _ =>
        }
        slice
      }
     
      /*
      Checks the statements for subslicing expressions
       */
      def checkStmt(s: in.Stmt): Boolean = s match {
        case s: in.If => checkExpr(s.cond) || checkStmt(s.thn) || checkStmt(s.els)
        case s: in.While =>  checkExpr(s.cond) || checkStmt(s.body)
        case s: in.SingleAss => checkExpr(s.right)
        case s: in.FunctionCall => s.args.exists(e => checkExpr(e))
        case s: in.MethodCall => s.args.exists(e => checkExpr(e))
        case _ => false
      }

     /* def createAnnotatedInfo(info: Source.Parser.Info): Source.Parser.Info =
        info match {
          case s: Single => s.createAnnotatedInfo(SlicingExpressionAnnotation)
          case i => violation(s"l.op.info ($i) is expected to be a Single")
        }*/

      members.foreach(checkBody)

    in.Program(
      types = p.types,
       members = p.members.diff(methodsToRemove.toSeq).appendedAll(methodsToAdd),
      table = p.table.merge(new in.LookupTable(definedFunctions = definedFunctionsDelta)),
    )(p.info)
  }
}
