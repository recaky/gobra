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
import viper.gobra.ast.internal.EncodingConfig

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
   var definedMPredicatesDelta: Map[in.MPredicateProxy, in.MPredicateLikeMember]= Map.empty
var definedFPredicatesDelta: Map[in.FPredicateProxy, in.FPredicateLikeMember] = Map.empty
   
 
  override def transform(p: in.Program): in.Program = p match {
    case in.Program(_, members, _) =>

      def checkBody(m: in.Member): Unit = {m match {
         case m: in.Method => {
          
         m.body match {
            case Some(in.MethodBody(_, seqn, _)) =>
              val member=m.asInstanceOf[in.Method];
              seqn.stmts.foreach(
                
                checkStmt(_,member.encodingConfig,p))
                
                
                val newMember= in.Method(member.receiver, member.name, member.args, member.results, member.pres, member.posts, member.terminationMeasures, member.body.map(a=>computeNewBody(a,member.encodingConfig,p)), member.encodingConfig )(member.info);
                
                methodsToAdd+= newMember;
                methodsToRemove+= m;}  }
        case m: in.Function => {
          
         m.body match {
            case Some(in.MethodBody(_, seqn, _)) =>
            val member=m.asInstanceOf[in.Function];
              seqn.stmts.foreach(
                
                {checkStmt(_,member.encodingConfig,p)})
              
                
                
                val newMember= in.Function(member.name, member.args, member.results, member.pres, member.posts, member.terminationMeasures, member.body.map(a=>computeNewBody(a,member.encodingConfig,p)) , member.encodingConfig)(member.info);
                
                
                methodsToAdd+= newMember;
                methodsToRemove+= m;}}
                
          case _=>   
                
                
          }
                

      
      
      
      }

     def checkStmt(s: in.Stmt, m:EncodingConfig, p: in.Program): Unit = {s match {
      case s@in.SingleAss(l,r)=> checkExpr(r,m,p)
      case s@in.Block(_,stmts) => stmts.map(a=> checkStmt(a,m,p))
      case s@in.Seqn(stmts) => stmts.map(a=> checkStmt(a,m,p))
      case i@in.If(cond, thn, els) => {checkExpr(cond,m,p);checkStmt(thn,m,p); checkStmt(els,m,p);}
      case w@in.While(cond, invs, terminationMeasure, body) => {checkExpr(cond,m,p);checkStmt(body,m,p);}
      case d@in.Defer(stmt)=> checkStmt(stmt,m,p)

      
      case s: in.FunctionCall => {
          val nameoffunction = in.FunctionProxy(s.func.name + m.config())(s.func.info)
            if (p.table.definedFunctions.contains(nameoffunction) || definedFunctionsDelta.contains(nameoffunction)) {}
            else {
              val function= (p.table.lookup(in.FunctionProxy(s.func.name + functionlookup(m, s.func, p).config())(s.func.info))).asInstanceOf[in.Function]
              var newMember= in.Function(nameoffunction, function.args, function.results, function.pres, function.posts, function.terminationMeasures, None,m)(function.info);
                
                methodsToAdd+= newMember; definedFunctionsDelta+= nameoffunction->newMember;
                }}
      case s: in.GoFunctionCall => {
          val nameoffunction = in.FunctionProxy(s.func.name + m.config())(s.func.info)
            if (p.table.definedFunctions.contains(nameoffunction) || definedFunctionsDelta.contains(nameoffunction)) {}
            else {
              val function= (p.table.lookup(in.FunctionProxy(s.func.name + functionlookup(m, s.func, p).config())(s.func.info))).asInstanceOf[in.Function]
              var newMember= in.Function(nameoffunction, function.args, function.results, function.pres, function.posts, function.terminationMeasures, None,m)(function.info);
               
                methodsToAdd+= newMember; definedFunctionsDelta+= nameoffunction->newMember;
                }}
                
      case s: in.MethodCall => {
            val nameofmethod = in.MethodProxy(s.meth.name + m.config(), s.meth.uniqueName + m.config)(s.meth.info)
              if (p.table.definedMethods.contains(nameofmethod) || definedMethodsDelta.contains(nameofmethod)) {}
            else {
              val method= (p.table.lookup(in.MethodProxy(s.meth.name + methodlookup(m, s.meth, p).config(), s.meth.uniqueName + methodlookup(m, s.meth, p).config())(s.meth.info))).asInstanceOf[in.Method]
              var newMember= in.Method(method.receiver, nameofmethod, method.args, method.results, method.pres, method.posts, method.terminationMeasures, None,m)(method.info);
             
               
                methodsToAdd+= newMember; definedMethodsDelta+= nameofmethod->newMember;
                }}
      case s: in.GoMethodCall => {
            val nameofmethod = in.MethodProxy(s.meth.name + m.config(), s.meth.uniqueName + m.config())(s.meth.info)
              if (p.table.definedMethods.contains(nameofmethod)|| definedMethodsDelta.contains(nameofmethod)) {}
            else {
              val method= (p.table.lookup(in.MethodProxy(s.meth.name + methodlookup(m, s.meth, p).config(), s.meth.uniqueName+ methodlookup(m, s.meth, p).config())(s.meth.info))).asInstanceOf[in.Method]
              var newMember= in.Method(method.receiver, nameofmethod, method.args, method.results, method.pres, method.posts, method.terminationMeasures, None,m)(method.info);
               
                methodsToAdd+= newMember; definedMethodsDelta+= nameofmethod->newMember;
                }}
      

      
       case _=>
                
        
      }}
      def transformStmt(s: in.Stmt, m:EncodingConfig,p:in.Program):in.Stmt= { s match {
          case s@in.SingleAss(l,r)=> {in.SingleAss(l,transformExpr(r,m,p))(s.info)}
          case s@in.Block(decls,stmts) => in.Block(decls,stmts.map(a=> transformStmt(a,m,p)))(s.info)
          case s@in.Seqn(stmts) => in.Seqn(stmts.map(a=> transformStmt(a,m,p)))(s.info)
          case i@in.If(cond, thn, els) => in.If(transformExpr(cond,m,p), transformStmt(thn,m,p),transformStmt(els,m,p))(i.info)
          case w@in.While(cond, invs, terminationMeasure, body) =>in.While(transformExpr(cond,m,p),invs, terminationMeasure, transformStmt(body,m,p))(w.info)
          case d@in.Defer(f@in.FunctionCall(targets,func,args)) => val nameoffunction = in.FunctionProxy(func.name + m.config() )(func.info);in.Defer(in.FunctionCall(targets,nameoffunction,args)(f.info))(d.info)
          case d@in.Defer(f@in.MethodCall(targets,recv,meth,args)) => val nameofmethod = in.MethodProxy(meth.name + m.config(), meth.uniqueName+ m.config())(meth.info);in.Defer(in.MethodCall(targets,recv,nameofmethod,args)(f.info))(d.info)
          
          case s@in.FunctionCall(targets,func,args) =>{  val nameoffunction = in.FunctionProxy(func.name + m.config())(func.info); in.FunctionCall (targets, nameoffunction,args)(s.info); }
          case s@in.GoFunctionCall(func, args) =>{  val nameoffunction = in.FunctionProxy(func.name + m.config())(func.info); in.GoFunctionCall ( nameoffunction,args)(s.info); }
          case s@in.MethodCall(targets, recv, meth, args) => { val nameofmethod = in.MethodProxy(meth.name + m.config(), meth.uniqueName+ m.config())(meth.info); in.MethodCall (targets,recv, nameofmethod,args)(s.info);}
          case s@in.GoMethodCall(recv,meth, args) =>{  val nameofmethod = in.MethodProxy(meth.name + m.config(), meth.uniqueName+ m.config())(meth.info); in.GoMethodCall (recv, nameofmethod,args)(s.info); }
          case s@in.Inhale(ass)=>in.Inhale(transformAssertion(ass,m,p))(s.info)
          case s@in.Exhale(ass)=>in.Exhale(transformAssertion(ass,m,p))(s.info)
          case s@in.Assert(ass)=>in.Assert(transformAssertion(ass,m,p))(s.info)
          case s@in.Assume(ass)=>in.Assume(transformAssertion(ass,m,p))(s.info)
          case s@in.Fold(in.Access(e,pr))=>{checkExpr(pr,m,p);in.Fold(in.Access(transformAccessible(e,m,p),transformExpr(pr,m,p))(s.info))(s.info)}
          case s@in.Unfold(in.Access(e,pr))=>{checkExpr(pr,m,p);in.Unfold(in.Access(transformAccessible(e,m,p),transformExpr(pr,m,p))(s.info))(s.info)}
          case _=> s





      }}
        def transformExpr(s:in.Expr, m:EncodingConfig,p:in.Program):in.Expr= { s match {
          case s@in.PureFunctionCall(func,args,typ) => {val nameoffunction = in.FunctionProxy(func.name + m.config())(func.info); in.PureFunctionCall (nameoffunction,args,typ)(s.info);}
          case s@in.PureMethodCall(recv,meth,args,typ) => {println("dobro");val nameofmethod = in.MethodProxy(meth.name + m.config(), meth.uniqueName + m.config())(meth.info); in.PureMethodCall (recv,nameofmethod,args,typ)(s.info);}

          case _=> s}}

        def transformAssertion (s:in.Assertion,m:EncodingConfig,p:in.Program):in.Assertion= { s match {
          case s@in.SepAnd(left, right)=> in.SepAnd(transformAssertion(left,m,p),transformAssertion(right,m,p))(s.info)
          case s@in.ExprAssertion(exp)=> {checkExpr(exp,m,p);in.ExprAssertion(transformExpr(exp,m,p))(s.info)}
          case s@in.Implication(left,right) => {checkExpr(left,m,p);in.Implication(transformExpr(left,m,p),transformAssertion(right,m,p))(s.info) }
          case s@in.Access(e,pr)=> {checkExpr(pr,m,p); in.Access(transformAccessible(e,m,p),transformExpr(pr,m,p))(s.info)}
          case _=> s
          }}

        
        def transformAccessible(s:in.Accessible,m:EncodingConfig, p:in.Program):in.Accessible = {
          s match {
           case s@in.Accessible.ExprAccess(op)=>{ checkExpr(op,m,p); in.Accessible.ExprAccess(transformExpr(op,m,p))}
           case s@in.Accessible.Predicate(op)=> {checkPredAccess(op,m,p);in.Accessible.Predicate(transformPredAccess(op,m,p))}
           case s@in.Accessible.PredExpr(pred@in.PredExprInstance(base,args))=>{checkExpr(base,m,p);args.map(a=> checkExpr(a,m,p));in.Accessible.PredExpr(in.PredExprInstance(transformExpr(base,m,p), args.map(a=>transformExpr(a,m,p)))(pred.info))}
           case _=> s






        }
   }
        def checkPredAccess(s:in.PredicateAccess,m:EncodingConfig,p:in.Program):Unit= {s match{
         case s@in.FPredicateAccess(pred,args) => {
         val nameofpredicate = in.FPredicateProxy(pred.name + m.config())(pred.info)
           if (p.table.definedFPredicates.contains(nameofpredicate) || definedFPredicatesDelta.contains(nameofpredicate)) {}
           else {
              val predicate= (p.table.lookup(in.FPredicateProxy(pred.name + fpredicatelookup(m, pred, p).config())(pred.info))).asInstanceOf[in.FPredicate]
              var newMember= in.FPredicate(nameofpredicate, predicate.args, None,m)(predicate.info);
                
                methodsToAdd+= newMember; definedFPredicatesDelta+= nameofpredicate->newMember;
             }}
        case s@in.MPredicateAccess(recv,pred,args) => {
         val nameofpredicate = in.MPredicateProxy(pred.name + m.config(), pred.uniqueName + m.config())(pred.info)
           if (p.table.definedMPredicates.contains(nameofpredicate) || definedMPredicatesDelta.contains(nameofpredicate)) {}
           else {
              val predicate= (p.table.lookup(in.MPredicateProxy(pred.name + mpredicatelookup(m, pred, p).config(), pred.uniqueName + mpredicatelookup(m, pred, p).config())(pred.info))).asInstanceOf[in.MPredicate]
              var newMember= in.MPredicate(predicate.receiver, nameofpredicate, predicate.args, None,m)(predicate.info);
                
                methodsToAdd+= newMember; definedMPredicatesDelta+= nameofpredicate->newMember;
             }}

        case _ =>

      


       }}
       def transformPredAccess (s:in.PredicateAccess, m:EncodingConfig,p:in.Program):in.PredicateAccess= {s match {
          case s@in.FPredicateAccess(pred,args)=> {args.map(a=>checkExpr(a,m,p));val name= in.FPredicateProxy(pred.name + m.config())(pred.info); in.FPredicateAccess(name, args.map(a=> transformExpr(a,m,p)))(s.info)}
          case s@in.MPredicateAccess(recv,pred,args)=> {args.map(a=>checkExpr(a,m,p));val name= in.MPredicateProxy(pred.name + m.config(),pred.uniqueName + m.config())(pred.info); in.MPredicateAccess(recv, name, args.map(a=> transformExpr(a,m,p)))(s.info)}
          case s@in.MemoryPredicateAccess(arg)=>{checkExpr(arg,m,p);in.MemoryPredicateAccess(transformExpr(arg,m,p))(s.info) }






        }} 
        def checkExpr (s:in.Expr, m:EncodingConfig, p:in.Program):Unit= { s match {
          case s: in.PureFunctionCall => {  val nameoffunction = in.FunctionProxy(s.func.name + m.config())(s.func.info)
            if (p.table.definedFunctions.contains(nameoffunction) || definedFunctionsDelta.contains(nameoffunction)) {}
            else {
              val function= (p.table.lookup(in.FunctionProxy(s.func.name + functionlookup(m, s.func, p).config())(s.func.info))).asInstanceOf[in.PureFunction]
              var newMember= in.PureFunction(nameoffunction, function.args, function.results, function.pres, function.posts, function.terminationMeasures, None,m)(function.info);
                
                methodsToAdd+= newMember; definedFunctionsDelta+= nameoffunction->newMember;
                }}

          case s: in.PureMethodCall => {
            val nameofmethod = in.MethodProxy(s.meth.name + m.config(), s.meth.uniqueName + m.config)(s.meth.info)
              if (p.table.definedMethods.contains(nameofmethod) || definedMethodsDelta.contains(nameofmethod)) {}
            else {
              val method= (p.table.lookup(in.MethodProxy(s.meth.name + methodlookup(m, s.meth, p).config(), s.meth.uniqueName + methodlookup(m, s.meth, p).config())(s.meth.info))).asInstanceOf[in.PureMethod]
              var newMember= in.PureMethod(method.receiver, nameofmethod, method.args, method.results, method.pres, method.posts, method.terminationMeasures, None,m)(method.info);
             
               
                methodsToAdd+= newMember; definedMethodsDelta+= nameofmethod->newMember;
                }}
          case _=>



        }}



     def computeNewBody(body: in.MethodBody, m:EncodingConfig,p:in.Program): in.MethodBody = {
    in.MethodBody(
      body.decls,
      in.MethodBodySeqn(body.seqn.stmts.map (a=> transformStmt(a,m,p)))(body.seqn.info),
      body.postprocessing.map (a=> transformStmt(a,m,p)),
    )(body.info)
  }

      


      def functionlookup (m:EncodingConfig, name: in.FunctionProxy, p:in.Program) : EncodingConfig = {
      var encodingConfig=m;
       for (i<-m.sliceEncodings) {if (p.table.definedFunctions.contains(in.FunctionProxy(name.name + "$" + i)(name.info))){encodingConfig= new EncodingConfig(i)}}
        encodingConfig}

      def methodlookup (m:EncodingConfig, name: in.MethodProxy, p:in.Program) : EncodingConfig = {
      var encodingConfig=m;
       for (i<-m.sliceEncodings) {if (p.table.definedMethods.contains(in.MethodProxy(name.name + "$" + i, name.uniqueName +  "$" + i)(name.info))){encodingConfig= new EncodingConfig(i)}}
        encodingConfig}
      def fpredicatelookup (m:EncodingConfig, name: in.FPredicateProxy, p:in.Program) : EncodingConfig = {
      var encodingConfig=m;
       for (i<-m.sliceEncodings) {if (p.table.definedFPredicates.contains(in.FPredicateProxy(name.name + "$" + i)(name.info))){encodingConfig= new EncodingConfig(i)}}
        encodingConfig}

      def mpredicatelookup (m:EncodingConfig, name: in.MPredicateProxy, p:in.Program) : EncodingConfig = {
      var encodingConfig=m;
       for (i<-m.sliceEncodings) {if (p.table.definedMPredicates.contains(in.MPredicateProxy(name.name + "$" + i, name.uniqueName +  "$" + i)(name.info))){encodingConfig= new EncodingConfig(i)}}
        encodingConfig}
     
     

     

      members.foreach(checkBody);
  
    in.Program(
      types = p.types,
      members = p.members.diff(methodsToRemove.toSeq).appendedAll(methodsToAdd),
      table = (p.table.merge(new in.LookupTable(definedFunctions = definedFunctionsDelta))).merge(new in.LookupTable(definedMethods = definedMethodsDelta)),
    )(p.info)
  }
}
