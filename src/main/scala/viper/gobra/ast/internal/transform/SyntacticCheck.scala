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
import viper.gobra.ast.internal.EncodingConfig

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
var definedMethodsDelta: Map[in.MethodProxy, in.MethodLikeMember] = Map.empty 
var definedMPredicatesDelta: Map[in.MPredicateProxy, in.MPredicateLikeMember]= Map.empty
var definedFPredicatesDelta: Map[in.FPredicateProxy, in.FPredicateLikeMember] = Map.empty
  /**
    * Program-to-program transformation
    */
  override def transform(p: in.Program): in.Program = p match {
    case in.Program(_, members, _) =>

      def checkBody(m: in.Member): Unit = m match {
        
        case m: in.Function =>{
          val number= random.nextInt(2);
          val config= new EncodingConfig(number);
          
          val function = in.Function(m.name,m.args,m.results,m.pres,m.posts,m.terminationMeasures, m.body,config)(m.info);
          methodsToRemove += m; methodsToAdd += function ; definedFunctionsDelta+= function.name->function
        
        
        
        }
        case m: in.PureFunction =>{
          val number= random.nextInt(2);
          val config= new EncodingConfig(number);
          val function = in.PureFunction(m.name,m.args,m.results,m.pres,m.posts,m.terminationMeasures, m.body, config)(m.info);
          
         
          methodsToRemove += m; methodsToAdd += function ; definedFunctionsDelta+= function.name->function
        
        
        
        }
         case m: in.Method =>{
          val number= random.nextInt(2);
          val config= new EncodingConfig(number);
         
          val method = in.Method(m.receiver,m.name,m.args,m.results,m.pres,m.posts,m.terminationMeasures, m.body,config )(m.info);
          
         
          methodsToRemove += m; methodsToAdd += method ; definedMethodsDelta+= method.name->method
        
        
        
        }
           case m: in.PureMethod =>{
            val number= random.nextInt(2);
            val config= new EncodingConfig(number);
        
          val method = in.PureMethod(m.receiver,m.name,m.args,m.results,m.pres,m.posts,m.terminationMeasures, m.body, config)(m.info);
         
         
          methodsToRemove += m; methodsToAdd += method ; definedMethodsDelta+= method.name->method
        
        
        
        }

        case m: in.MPredicate =>{
          val number= random.nextInt(2);
          val config= new EncodingConfig(number);
          
          val predicate = in.MPredicate(m.receiver,m.name,m.args, m.body, config)(m.info);
          
         
          methodsToRemove += m; methodsToAdd += predicate ; definedMPredicatesDelta+= predicate.name->predicate
        
        
        
        }
        case m: in.FPredicate =>{
          val number= random.nextInt(2);
          val config= new EncodingConfig(number);
          var predicate = in.FPredicate(m.name,m.args, m.body, config)(m.info);
          
         
          methodsToRemove += m; methodsToAdd += predicate ; definedFPredicatesDelta+= predicate.name->predicate
        
        
        
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
      table = p.table.merge(new in.LookupTable(definedMethods = definedMethodsDelta)).merge(new in.LookupTable(definedFunctions = definedFunctionsDelta)).merge(new in.LookupTable(definedMPredicates = definedMPredicatesDelta)).merge(new in.LookupTable(definedFPredicates = definedFPredicatesDelta)),
    )(p.info)
  }
}
