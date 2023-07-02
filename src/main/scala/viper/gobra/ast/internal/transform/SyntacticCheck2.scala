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
  var methodsToRemove: Set[in.Member]= Set.empty
   var definedFunctionsDelta: Map[in.FunctionProxy, in.FunctionLikeMember] = Map.empty 
   var definedMethodsDelta: Map [in.MethodProxy, in.MethodLikeMember]= Map.empty
  /**
    * Program-to-program transformation
    */
  override def transform(p: in.Program): in.Program = p match {
    case in.Program(_, members, _) =>

      def checkBody(m: in.Member): Unit = {m match {
         case m: in.Method => {
         m.body match {
            case Some(in.MethodBody(_, seqn, _)) =>
            val ann= m.Moje.slices;
              seqn.stmts.foreach(
                checkStmt(_,ann,p))}
                val member=m.asInstanceOf[in.Method];
                val ann= m.Moje.slices;
                val newMember= in.Method(member.receiver, member.name, member.args, member.results, member.pres, member.posts, member.terminationMeasures, member.body.map(a=>computeNewBody(a,ann)) )(member.info);
                newMember.Moje.setslices(m.Moje.slices);
                methodsToAdd+= newMember;
                methodsToRemove+= m;}  
        case m: in.Function => {
         m.body match {
            case Some(in.MethodBody(_, seqn, _)) =>
            val ann= m.Moje.slices;
              seqn.stmts.foreach(
                {checkStmt(_,ann,p)})}
              
                val member=m.asInstanceOf[in.Function];
                val ann= m.Moje.slices;
                val newMember= in.Function(member.name, member.args, member.results, member.pres, member.posts, member.terminationMeasures, member.body.map(a=>computeNewBody(a,ann)) )(member.info);
                
                newMember.Moje.setslices(m.Moje.slices);
                methodsToAdd+= newMember;
                methodsToRemove+= m;}
       
           
  
                
                
                
                
                
                
                
                
                
          }
                

      
      
      
      }

     def checkStmt(s: in.Stmt, m:Integer, p: in.Program): Unit = {s match {
       case s@in.Block(_,stmts) => stmts.map(a=> checkStmt(a,m,p))
       case s@in.Seqn(stmts) => stmts.map(a=> checkStmt(a,m,p))
      case i@in.If(cond, thn, els) => {checkStmt(thn,m,p); checkStmt(els,m,p);}
      case w@in.While(cond, invs, terminationMeasure, body) => {checkStmt(body,m,p);}
      case d@in.Defer(stmt)=> checkStmt(stmt,m,p)


      case s: in.FunctionCall => {
          val nameoffunction = in.FunctionProxy(s.func.name + "$" + m)(s.func.info)
            if (p.table.definedFunctions.contains(nameoffunction)) {}
            else {
              val function= (p.table.lookup(in.FunctionProxy(s.func.name + "$" + flip(m))(s.func.info))).asInstanceOf[in.Function]
              var newMember= in.Function(nameoffunction, function.args, function.results, function.pres, function.posts, function.terminationMeasures, None)(function.info);
               newMember.Moje.setslices(m);
                methodsToAdd+= newMember; definedFunctionsDelta+= nameoffunction->newMember;
                }}
      case s: in.GoFunctionCall => {
          val nameoffunction = in.FunctionProxy(s.func.name + "$" + m)(s.func.info)
            if (p.table.definedFunctions.contains(nameoffunction)) {}
            else {
              val function= (p.table.lookup(in.FunctionProxy(s.func.name + "$" + flip(m))(s.func.info))).asInstanceOf[in.Function]
              var newMember= in.Function(nameoffunction, function.args, function.results, function.pres, function.posts, function.terminationMeasures, None)(function.info);
               newMember.Moje.setslices(m);
                methodsToAdd+= newMember; definedFunctionsDelta+= nameoffunction->newMember;
                }}
                
      case s: in.MethodCall => {
            val nameofmethod = in.MethodProxy(s.meth.name + "$" + m, s.meth.uniqueName + "$" + m)(s.meth.info)
              if (p.table.definedMethods.contains(nameofmethod)) {}
            else {
              val method= (p.table.lookup(in.MethodProxy(s.meth.name + "$" + flip(m), s.meth.uniqueName+ "$" + flip(m))(s.meth.info))).asInstanceOf[in.Method]
              var newMember= in.Method(method.receiver, nameofmethod, method.args, method.results, method.pres, method.posts, method.terminationMeasures, None)(method.info);
              println("check" + m);
               newMember.Moje.setslices(m);
                methodsToAdd+= newMember; definedMethodsDelta+= nameofmethod->newMember;
                }}
      case s: in.GoMethodCall => {
            val nameofmethod = in.MethodProxy(s.meth.name + "$" + m, s.meth.uniqueName + "$" + m)(s.meth.info)
              if (p.table.definedMethods.contains(nameofmethod)) {}
            else {
              val method= (p.table.lookup(in.MethodProxy(s.meth.name + "$" + flip(m), s.meth.uniqueName+ "$" + flip(m))(s.meth.info))).asInstanceOf[in.Method]
              var newMember= in.Method(method.receiver, nameofmethod, method.args, method.results, method.pres, method.posts, method.terminationMeasures, None)(method.info);
               newMember.Moje.setslices(m);
                methodsToAdd+= newMember; definedMethodsDelta+= nameofmethod->newMember;
                }}
      
       case _=>
                
        
      }}
      def transformStmt(s: in.Stmt, m:Integer):in.Stmt= { s match {
          case s@in.Block(decls,stmts) => in.Block(decls,stmts.map(a=> transformStmt(a,m)))(s.info)
          case s@in.Seqn(stmts) => in.Seqn(stmts.map(a=> transformStmt(a,m)))(s.info)
          case i@in.If(cond, thn, els) => in.If(cond, transformStmt(thn,m),transformStmt(els,m))(i.info)
          case w@in.While(cond, invs, terminationMeasure, body) =>in.While(cond,invs, terminationMeasure, transformStmt(body,m))(w.info)
          case d@in.Defer(f@in.FunctionCall(targets,func,args)) => val nameoffunction = in.FunctionProxy(func.name + "$" + m)(func.info);in.Defer(in.FunctionCall(targets,nameoffunction,args)(f.info))(d.info)
          case s@in.FunctionCall(targets,func,args) =>{  val nameoffunction = in.FunctionProxy(func.name + "$" + m)(func.info); in.FunctionCall (targets, nameoffunction,args)(s.info); }
          case s@in.GoFunctionCall(func, args) =>{  val nameoffunction = in.FunctionProxy(func.name + "$" + m)(func.info); in.GoFunctionCall ( nameoffunction,args)(s.info); }
          case s@in.MethodCall(targets, recv, meth, args) => { val nameofmethod = in.MethodProxy(meth.name + "$" + m, meth.uniqueName+ "$" + m)(meth.info); in.MethodCall (targets,recv, nameofmethod,args)(s.info);}
          case s@in.GoMethodCall(recv,meth, args) =>{  val nameofmethod = in.MethodProxy(meth.name + "$" + m, meth.uniqueName+ "$" + m)(meth.info); in.GoMethodCall (recv, nameofmethod,args)(s.info); }

          case _=> s





      }}
     def computeNewBody(body: in.MethodBody, m:Integer): in.MethodBody = {
    in.MethodBody(
      body.decls,
      in.MethodBodySeqn(body.seqn.stmts.map (a=> transformStmt(a,m)))(body.seqn.info),
      body.postprocessing,
    )(body.info)
  }

      def flip(num: Integer): Integer = {
        if (num == 0) {
          1
        }
        else if (num == 1) {
          0
        }
        else num
      }
     

     

      members.foreach(checkBody);
  
    in.Program(
      types = p.types,
      members = p.members.diff(methodsToRemove.toSeq).appendedAll(methodsToAdd),
      table = (p.table.merge(new in.LookupTable(definedFunctions = definedFunctionsDelta))).merge(new in.LookupTable(definedMethods = definedMethodsDelta)),
    )(p.info)
  }
}
