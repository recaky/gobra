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

/**
  * Transformation responsible for generating call-graph edges from interface methods to their implementations' methods.
  * This is necessary to soundly verify termination in the presence of dynamic method binding.
  */
object SyntacticCheck2 extends InternalTransform {
  override def name(): String = "syntactic_check_for_interface"
  var methodsToAdd: Set[in.Member] = Set.empty
  /**
    * Program-to-program transformation
    */
  override def transform(p: in.Program): in.Program = p match {
    case in.Program(_, members, _) =>

      def checkBody(m: in.Member): Unit = m match {
        case m: in.Function =>
        
          m.body match {
            case Some(in.MethodBody(_, seqn, _)) =>
              seqn.stmts.foreach(
                s => s.visit {
                 chechSameEncoding(s,m,p);
              })
              println("The function " + m.name + " does not contain subslicing expressions")
              m.Annotation.setslices(1)
              println(m.Annotation.slices)
            case _ => m.Annotation.setslices(1) 
          }
        case _ =>
      }

      /*
      Checks the expressions for subslicing expressions
       */
      def checkExpr(e: in.Expr, m:in.Member, p:in.Program): Boolean = {
        var same = true
        e.visit {
          case elem: in.FunctionLitLike => {
 val member = elem.asInstanceOf[in.Function];
        if (member.Annotation.slices==m.Annotation.slices) {true} else {
          val newMember = in.Function( member.name, member.args, member.results, member.pres, member.posts, member.terminationMeasures, None)(member.info);
          methodsToAdd += newMember;
          false


}





          }
          case _ =>
        }
        slice
      }
     
      /*
      Checks the statements for subslicing expressions
       */
      def checkSameEncoding(s: in.Stmt, m: in.Member, p: in.Program):Boolean = 
      s match {
        case s: in.If => checkExpr(s.cond,m ,p) && checkSameEncoding(s.thn,m,p) && checkSameEncoding(s.els,m,p)
        case s: in.While =>  checkExpr(s.cond,m,p) && checkSameEncoding(s.body,m,p)
        case s: in.SingleAss => checkExpr(s.right,m,p)
        case s: in.FunctionCall => {
        val member = p.table.lookup(s.func).asInstanceOf[in.Function];
        if (member.Annotation.slices==m.Annotation.slices) {true} else {

            


          val newMember = in.Function( member.name, member.args, member.results, member.pres, member.posts, member.terminationMeasures, None)(member.info);
          methodsToAdd += newMember;
          false


}






        }
        case s: in.MethodCall => {
        val member = p.table.lookup(s.meth).asInstanceOf[in.Method];
        if (member.Annotation.slices==m.Annotation.slices) {true} else {
        val newMember = in.Method( member.receiver, member.name, member.args, member.results, member.pres, member.posts, member.terminationMeasures, None)(member.info)
        methodsToAdd += newMember;
        false
                
}






        }
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
      members = p.members,
      table = p.table,
    )(p.info)
  }
}
