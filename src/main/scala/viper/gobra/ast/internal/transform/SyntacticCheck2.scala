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
                methodsToRemove+= m;
                case None=>None
                }  }
        case m: in.Function => {
          
         m.body match {
            case Some(in.MethodBody(_, seqn, _)) =>
            val member=m.asInstanceOf[in.Function];
              seqn.stmts.foreach(
                
                {checkStmt(_,member.encodingConfig,p)})
              
                
                
                val newMember= in.Function(member.name, member.args, member.results, member.pres, member.posts, member.terminationMeasures, member.body.map(a=>computeNewBody(a,member.encodingConfig,p)) , member.encodingConfig)(member.info);
                
                
                methodsToAdd+= newMember;
                methodsToRemove+= m;
                case None=>None}}
        case m: in.PureFunction => {
          
         m.body match {
            case Some(a) =>
            val member=m.asInstanceOf[in.PureFunction];
              checkExpr(a,member.encodingConfig,p);
              
                
                
                val newMember= in.PureFunction(member.name, member.args, member.results, member.pres, member.posts, member.terminationMeasures, computeNewExprBody(member.body,member.encodingConfig,p) , member.encodingConfig)(member.info);
                
                
                methodsToAdd+= newMember;
                methodsToRemove+= m;
                case None=>None}}
          case m: in.PureMethod => {
          
         m.body match {
            case Some(a) =>
              val member=m.asInstanceOf[in.PureMethod];
              checkExpr(a,member.encodingConfig,p);
                
                
                val newMember= in.PureMethod(member.receiver, member.name, member.args, member.results, member.pres, member.posts, member.terminationMeasures, computeNewExprBody(member.body,member.encodingConfig,p), member.encodingConfig )(member.info);
                
                methodsToAdd+= newMember;
                methodsToRemove+= m;
                case None=>None
                }  }
          case m: in.MPredicate => {
          
         m.body match {
            case Some(a) =>
              val member=m.asInstanceOf[in.MPredicate];
              
                
                
                val newMember= in.MPredicate(member.receiver, member.name, member.args, computeNewAssBody(member.body,member.encodingConfig,p), member.encodingConfig )(member.info);
                
                methodsToAdd+= newMember;
                methodsToRemove+= m;
                case None=>None
                }  }
        case m: in.FPredicate => {
          
         m.body match {
            case Some(a) =>
              val member=m.asInstanceOf[in.FPredicate];
              
                
                
                val newMember= in.FPredicate( member.name, member.args, computeNewAssBody(member.body,member.encodingConfig,p), member.encodingConfig )(member.info);
                
                methodsToAdd+= newMember;
                methodsToRemove+= m;
                case None=>None
                }  }
                
                
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
      def transformStmt(s: in.Stmt, m:EncodingConfig,p:in.Program):in.Stmt= {println(s + "-" + s.getClass);s match {

          case s@in.SingleAss(l,r)=> {in.SingleAss(l,transformExpr(r,m,p))(s.info)}
          case s@in.Block(decls,stmts) => in.Block(decls,stmts.map(a=> transformStmt(a,m,p)))(s.info)
          case s@in.Seqn(stmts) => in.Seqn(stmts.map(a=> transformStmt(a,m,p)))(s.info)
          case i@in.If(cond, thn, els) => in.If(transformExpr(cond,m,p), transformStmt(thn,m,p),transformStmt(els,m,p))(i.info)
          case w@in.While(cond, invs, terminationMeasure, body) =>in.While(transformExpr(cond,m,p),invs.map(a=>transformAssertion(a,m,p)), terminationMeasure, transformStmt(body,m,p))(w.info)
          case d@in.Defer(f@in.FunctionCall(targets,func,args)) => val nameoffunction = in.FunctionProxy(func.name + m.config() )(func.info);in.Defer(in.FunctionCall(targets,nameoffunction,args)(f.info))(d.info)
          case d@in.Defer(f@in.MethodCall(targets,recv,meth,args)) => val nameofmethod = in.MethodProxy(meth.name + m.config(), meth.uniqueName+ m.config())(meth.info);in.Defer(in.MethodCall(targets,recv,nameofmethod,args)(f.info))(d.info)
          case d@in.Defer(s@in.Fold(a@in.Access(e,pr)))=>{checkExpr(pr,m,p);in.Defer(in.Fold(in.Access(transformAccessible(e,m,p),transformExpr(pr,m,p))(a.info))(s.info))(d.info)}
          case d@in.Defer(s@in.Unfold(a@in.Access(e,pr)))=>{checkExpr(pr,m,p);in.Defer(in.Unfold(in.Access(transformAccessible(e,m,p),transformExpr(pr,m,p))(a.info))(s.info))(d.info)}
          case s@in.SafeMapLookup(res,succ,d@in.IndexedExp(base,ind,typ))=>{checkExpr(base,m,p);checkExpr(ind,m,p);in.SafeMapLookup(res,succ,in.IndexedExp(transformExpr(base,m,p),transformExpr(ind,m,p),typ)(d.info))(s.info)}
          case s@in.FunctionCall(targets,func,args) =>{  val nameoffunction = in.FunctionProxy(func.name + m.config())(func.info); in.FunctionCall (targets, nameoffunction,args)(s.info); }
          case s@in.GoFunctionCall(func, args) =>{  val nameoffunction = in.FunctionProxy(func.name + m.config())(func.info); in.GoFunctionCall ( nameoffunction,args)(s.info); }
          case s@in.MethodCall(targets, recv, meth, args) => { val nameofmethod = in.MethodProxy(meth.name + m.config(), meth.uniqueName+ m.config())(meth.info); in.MethodCall (targets,recv, nameofmethod,args)(s.info);}
          case s@in.GoMethodCall(recv,meth, args) =>{  val nameofmethod = in.MethodProxy(meth.name + m.config(), meth.uniqueName+ m.config())(meth.info); in.GoMethodCall (recv, nameofmethod,args)(s.info); }
          case s@in.Inhale(ass)=>in.Inhale(transformAssertion(ass,m,p))(s.info)
          case s@in.Exhale(ass)=>in.Exhale(transformAssertion(ass,m,p))(s.info)
          case s@in.Assert(ass)=>in.Assert(transformAssertion(ass,m,p))(s.info)
          case s@in.Assume(ass)=>in.Assume(transformAssertion(ass,m,p))(s.info)
          case s@in.Fold(a@in.Access(e,pr))=>{checkExpr(pr,m,p);in.Fold(in.Access(transformAccessible(e,m,p),transformExpr(pr,m,p))(a.info))(s.info)}
          case s@in.Unfold(a@in.Access(e,pr))=>{checkExpr(pr,m,p);in.Unfold(in.Access(transformAccessible(e,m,p),transformExpr(pr,m,p))(a.info))(s.info)}
          case s@in.MakeMap(target,typeParam,Some(init))=> {checkExpr(init,m,p);in.MakeMap(target,typeParam,Some(transformExpr(init,m,p)))(s.info)}
          case s@in.MakeSlice(target,typeParam,lenArg,Some(capArg))=> {checkExpr(lenArg,m,p);checkExpr(capArg,m,p);in.MakeSlice(target,typeParam,transformExpr(lenArg,m,p),Some(transformExpr(capArg,m,p)))(s.info)}
          case s@in.New(target,expr)=>{checkExpr(expr,m,p); in.New(target,transformExpr(expr,m,p))(s.info)}
          case s@in.Outline(name,pres,posts,tm,body,trusted)=> {checkStmt(body,m,p);in.Outline(name,pres,posts,tm,transformStmt(body,m,p),trusted)(s.info)}
          case s@in.SafeTypeAssertion(res,succ,expr,typ)=>{checkExpr(expr,m,p);in.SafeTypeAssertion(res,succ,transformExpr(expr,m,p),typ)(s.info) }
          case s@in.EffectfulConversion(target,newType, expr)=> checkExpr(expr,m,p); in.EffectfulConversion(target,newType,transformExpr(expr,m,p))(s.info)
          case s@in.PackageWand(d@in.MagicWand(left,right), block)=> in.PackageWand(in.MagicWand(transformAssertion(left,m,p), transformAssertion(right,m,p))(d.info), (block match {case Some(a)=>checkStmt(a,m,p); Some(transformStmt(a,m,p))
                                                                                                                                                                                                                  case None=> None        }))(s.info)
          case s@in.ApplyWand(d@in.MagicWand(left,right))=>in.ApplyWand(in.MagicWand(transformAssertion(left,m,p), transformAssertion(right,m,p))(d.info))(s.info) 
          case s@in.PatternMatchStmt(exp, cases, strict)=> checkExpr(exp,m,p); in.PatternMatchStmt(transformExpr(exp,m,p), cases.map(a=> a match{ case f@in.PatternMatchCaseStmt(mExp,body)=> {checkStmt(body,m,p); in.PatternMatchCaseStmt(handleMPattern(mExp,m,p),transformStmt(body,m,p))(f.info)} 
                                                                                                                                              case _=>a} ),strict)(s.info)  
          case s@in.PredExprFold(d@in.PredicateConstructor(proxy,proxyT,arg),args,pi)=> args.map(a=>checkExpr(a,m,p));checkExpr(pi,m,p); in.PredExprFold(in.PredicateConstructor(handleProxy(proxy,m,p),proxyT,arg.map(a=> a match {case Some(ex)=>{checkExpr(ex,m,p);Some(transformExpr(ex,m,p))}case None=>None}))(d.info),args.map(a=> transformExpr(a,m,p)),transformExpr(pi,m,p))(s.info)                                                                                                                                                                        
          case s@in.PredExprUnfold(d@in.PredicateConstructor(proxy,proxyT,arg),args,pi)=> args.map(a=>checkExpr(a,m,p));checkExpr(pi,m,p); in.PredExprUnfold(in.PredicateConstructor(handleProxy(proxy,m,p),proxyT,arg.map(a=> a match {case Some(ex)=>{checkExpr(ex,m,p);Some(transformExpr(ex,m,p))}case None=>None}))(d.info),args.map(a=> transformExpr(a,m,p)),transformExpr(pi,m,p))(s.info)                                                                                                                                                                        
          case _=> s





      }}
       def handleProxy(s:in.PredicateProxy, m:EncodingConfig, p:in.Program):in.PredicateProxy= {s match{
          case s@in.FPredicateProxy(name)=> in.FPredicateProxy(name + m.config())(s.info)
          case s@in.MPredicateProxy(name, uniqueName)=> in.MPredicateProxy(name+ m.config, uniqueName + m.config())(s.info)
          case _=> s




       }}

       def handleMPattern(s:in.MatchPattern, m:EncodingConfig, p:in.Program): in.MatchPattern= {s match {
    case s@in.MatchValue(exp)=> checkExpr(exp,m,p); in.MatchValue(transformExpr(exp,m,p))(s.info)
    case s@in.MatchAdt(clause,expr)=>  in.MatchAdt(clause,expr.map(a=> handleMPattern(a,m,p)))(s.info)
    case _=> s}}
     /*def handleTM(s:in.TerminationMeasure,m:EncodingConfig,p:in.Program): in.TerminationMeasure= s match{
      case s@in.WildcardMeasure(cond)=> in.WildcardMeasure(cond match {case Some(exp)=>checkExpr(exp,m,p); Some(transformExpr(exp,m,p))})(s.info)






     }*/
        def transformExpr(s:in.Expr, m:EncodingConfig,p:in.Program):in.Expr= {s match {
          case s@in.PatternMatchExp(exp,typ,cases,default)=> checkExpr(exp,m,p); in.PatternMatchExp(transformExpr(exp,m,p),typ,cases,(default match{case Some(a)=>checkExpr(a,m,p);Some(transformExpr(a,m,p))
                                                                                                                                           case None=> None}))(s.info)
        //  case s@in.Let(left,right,in)=> checkExpr(right,m,p);checkExpr(in,m,p)=> in.Let(left,transformExpr(right,m,p),transformExpr(in,m,p))(s.info)  
          case s@in.PureFunctionCall(func,args,typ) => {val nameoffunction = in.FunctionProxy(func.name + m.config())(func.info); in.PureFunctionCall (nameoffunction,args,typ)(s.info);}
          case s@in.PureMethodCall(recv,meth,args,typ) => {val nameofmethod = in.MethodProxy(meth.name + m.config(), meth.uniqueName + m.config())(meth.info); in.PureMethodCall (recv,nameofmethod,args,typ)(s.info);}
          case s@in.EqCmp(left,right)=>checkExpr(left,m,p);checkExpr(right,m,p); in.EqCmp(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.UneqCmp(left,right)=>checkExpr(left,m,p);checkExpr(right,m,p); in.UneqCmp(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.GhostEqCmp(left,right)=> checkExpr(left,m,p);checkExpr(right,m,p);in.GhostEqCmp(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.LessCmp(left,right)=>checkExpr(left,m,p);checkExpr(right,m,p); in.LessCmp(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.AtMostCmp(left,right)=>checkExpr(left,m,p);checkExpr(right,m,p); in.AtMostCmp(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.GreaterCmp(left,right)=>checkExpr(left,m,p);checkExpr(right,m,p); in.GreaterCmp(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.AtLeastCmp(left,right)=> checkExpr(left,m,p);checkExpr(right,m,p);in.AtLeastCmp(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.And(left,right)=>checkExpr(left,m,p);checkExpr(right,m,p); in.And(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.Or(left,right)=> checkExpr(left,m,p);checkExpr(right,m,p);in.Or(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.Add(left,right)=> checkExpr(left,m,p);checkExpr(right,m,p);in.Add(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.Sub(left,right)=> checkExpr(left,m,p);checkExpr(right,m,p);in.Sub(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.Mul(left,right)=> checkExpr(left,m,p);checkExpr(right,m,p);in.Mul(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.Mod(left,right)=> checkExpr(left,m,p);checkExpr(right,m,p);in.Mod(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.Div(left,right)=> checkExpr(left,m,p);checkExpr(right,m,p);in.Div(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.BitAnd(left,right)=>checkExpr(left,m,p);checkExpr(right,m,p); in.BitAnd(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.BitOr(left,right)=> checkExpr(left,m,p);checkExpr(right,m,p);in.BitOr(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.BitXor(left,right)=> checkExpr(left,m,p);checkExpr(right,m,p);in.BitXor(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.BitClear(left,right)=> checkExpr(left,m,p);checkExpr(right,m,p);in.BitClear(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.ShiftLeft(left,right)=> checkExpr(left,m,p);checkExpr(right,m,p);in.ShiftLeft(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.ShiftRight(left,right)=> checkExpr(left,m,p);checkExpr(right,m,p);in.ShiftRight(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.BitNeg(op)=> checkExpr(op,m,p);in.BitNeg(transformExpr(op,m,p))(s.info)
          case s@in.TypeAssertion(exp,arg)=> checkExpr(exp,m,p);in.TypeAssertion(transformExpr(exp,m,p),arg)(s.info)
          case s@in.TypeOf(exp)=>checkExpr(exp,m,p);in.TypeOf(transformExpr(exp,m,p))(s.info)
          case s@in.IsComparableType(exp)=>checkExpr(exp,m,p);in.IsComparableType(transformExpr(exp,m,p))(s.info)
          case s@in.IsComparableInterface(exp)=>checkExpr(exp,m,p); in.IsComparableInterface(transformExpr(exp,m,p))(s.info)
          case s@in.IsBehaviouralSubtype(sub,spr)=>checkExpr(sub,m,p);checkExpr(spr,m,p);in.IsBehaviouralSubtype(transformExpr(sub,m,p),transformExpr(spr,m,p))(s.info)
          case s@in.ToInterface(exp,typ)=>checkExpr(exp,m,p);in.ToInterface(transformExpr(exp,m,p),typ)(s.info)
          case s@in.PointerTExpr(elems)=> checkExpr(elems,m,p); in.PointerTExpr(transformExpr(elems,m,p))(s.info)
          case s@in.StructTExpr(fields)=> fields.map( field=> checkExpr(field._2,m,p)); in.StructTExpr( fields.map(field=> (field._1,transformExpr(field._2,m,p),field._3)))(s.info)
          case s@in.ArrayTExpr(length,elems)=> checkExpr(length,m,p); checkExpr(elems,m,p); in.ArrayTExpr(transformExpr(length,m,p),transformExpr(elems,m,p))(s.info)
          case s@in.SliceTExpr(elems)=> checkExpr(elems,m,p); in.SliceTExpr(transformExpr(elems,m,p))(s.info)
          case s@in.MapTExpr(keys,elems)=> checkExpr(elems,m,p);checkExpr(keys,m,p);in.MapTExpr(transformExpr(keys,m,p),transformExpr(elems,m,p))(s.info)
          case s@in.SequenceTExpr(elems)=> checkExpr(elems,m,p);in.SequenceTExpr(transformExpr(elems,m,p))(s.info)
          case s@in.SetTExpr(elems)=> checkExpr(elems,m,p);in.SetTExpr(transformExpr(elems,m,p))(s.info)
          case s@in.MultisetTExpr(elems)=> checkExpr(elems,m,p);in.MultisetTExpr(transformExpr(elems,m,p))(s.info)
          case s@in.OptionTExpr(elems)=> checkExpr(elems,m,p);in.OptionTExpr(transformExpr(elems,m,p))(s.info)
          case s@in.MathMapTExpr(keys,elems)=> checkExpr(elems,m,p);checkExpr(keys,m,p);in.MathMapTExpr(transformExpr(keys,m,p),transformExpr(elems,m,p))(s.info)
          case s@in.TupleTExpr(elems)=> elems.map(a=> checkExpr(a,m,p)); in.TupleTExpr(elems.map(a=> transformExpr(a,m,p)))(s.info)
          case s@in.OptionSome(exp)=> checkExpr(exp,m,p); in.OptionSome(transformExpr(exp,m,p))(s.info)
          case s@in.OptionGet(exp)=> checkExpr(exp,m,p);in.OptionGet(transformExpr(exp,m,p))(s.info)
          case s@in.Multiplicity(left,right)=> checkExpr(left,m,p); checkExpr(right,m,p); in.Multiplicity(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.Length(exp)=> checkExpr(exp,m,p);in.Length(transformExpr(exp,m,p))(s.info)
          case s@in.Capacity(exp)=> checkExpr(exp,m,p);in.Capacity(transformExpr(exp,m,p))(s.info)
          case s@in.IndexedExp(base,index,basetyp)=> checkExpr(base,m,p);checkExpr(index,m,p); in.IndexedExp(transformExpr(base,m,p),transformExpr(index,m,p),basetyp)(s.info)
          case s@in.ArrayUpdate(base,left,right)=> checkExpr(base,m,p);checkExpr(left,m,p);checkExpr(right,m,p);in.ArrayUpdate(transformExpr(base,m,p),transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.RangeSequence(left,right)=> checkExpr(left,m,p); checkExpr(right,m,p); in.RangeSequence(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.SequenceAppend(left,right)=> checkExpr(left,m,p); checkExpr(right,m,p); in.SequenceAppend(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.GhostCollectionUpdate(base,left,right,basetyp)=> checkExpr(base,m,p);checkExpr(left,m,p);checkExpr(right,m,p); in.GhostCollectionUpdate(transformExpr(base,m,p),transformExpr(left,m,p),transformExpr(right,m,p),basetyp)(s.info)
          case s@in.SequenceDrop(left,right)=> checkExpr(left,m,p); checkExpr(right,m,p); in.SequenceDrop(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.SequenceTake(left,right)=> checkExpr(left,m,p); checkExpr(right,m,p); in.SequenceTake(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.SequenceConversion(exp)=> checkExpr(exp,m,p);in.SequenceConversion(transformExpr(exp,m,p))(s.info)
          case s@in.Union(left,right)=> checkExpr(left,m,p); checkExpr(right,m,p); in.Union(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.Intersection(left,right)=> checkExpr(left,m,p); checkExpr(right,m,p); in.Intersection(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.SetMinus(left,right)=> checkExpr(left,m,p); checkExpr(right,m,p); in.SetMinus(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.Subset(left,right)=> checkExpr(left,m,p); checkExpr(right,m,p); in.Subset(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case s@in.Contains(left,right)=> checkExpr(left,m,p); checkExpr(right,m,p); in.Contains(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
         // case s@in.Lit.Setlit(mem,exprs)=> exprs.map(a=> checkExpr(a,m,p)); in.CompositeLit.Setlit(mem,exprs.map(a=>transformExpr(a,m,p)))(s.info)
          case s@in.SetConversion(exp)=> checkExpr(exp,m,p);in.SetConversion(transformExpr(exp,m,p))(s.info)
          //case s@in.Multisetlit(mem,exprs)=> exprs.map(a=> checkExpr(a,m,p)); in.Multisetlit(mem,exprs.map(a=>transformExpr(a,m,p)))(s.info)
          case s@in.MultisetConversion(exp)=> checkExpr(exp,m,p);in.MultisetConversion(transformExpr(exp,m,p))(s.info)
          case s@in.MapKeys(exp,etyp)=> checkExpr(exp,m,p);in.MapKeys(transformExpr(exp,m,p),etyp)(s.info)
          case s@in.MapValues(exp,etyp)=> checkExpr(exp,m,p);in.MapValues(transformExpr(exp,m,p),etyp)(s.info)
          case s@in.Deref(exp,etyp)=> checkExpr(exp,m,p);in.Deref(transformExpr(exp,m,p),etyp)(s.info)
          case s@in.Ref(ref,typ) => in.Ref(transformAddressable(ref,m,p),typ)(s.info)
          case s@in.FieldRef(recv,field)=> checkExpr(recv,m,p); in.FieldRef(transformExpr(recv,m,p),field)(s.info)
          case s@in.StructUpdate (base,field,newval)=> checkExpr(base,m,p); checkExpr(newval,m,p); in.StructUpdate(transformExpr(base,m,p),field,transformExpr(newval,m,p))(s.info)
          case s@in.AdtDestructor(base,field) => checkExpr(base,m,p); in.AdtDestructor(transformExpr(base,m,p), field)(s.info)
          case s@in.AdtDiscriminator(base,clause)=>checkExpr(base,m,p); in.AdtDiscriminator(transformExpr(base,m,p),clause)(s.info)
          case s@in.Negation(exp)=> checkExpr(exp,m,p); in.Negation(transformExpr(exp,m,p))(s.info)
          case s@in.Conversion(newType, exp)=> checkExpr(exp,m,p); in.Conversion(newType, transformExpr(exp,m,p))(s.info)
          case s@in.Slice(base,low,high,max,basetyp)=>checkExpr(base,m,p);checkExpr(low,m,p);checkExpr(high,m,p); in.Slice(transformExpr(base,m,p),transformExpr(low,m,p),transformExpr(high,m,p),(max match{case Some(a)=> checkExpr(a,m,p);Some(transformExpr(a,m,p))
                                                                                                                                                                                                          case None=> None}),basetyp)(s.info)
          case s@in.Tuple(args)=> args.map(a=> checkExpr(a,m,p)); in.Tuple(args.map(a=> transformExpr(a,m,p)))(s.info)
          case s@in.PatternMatchExp(exp,typ, cases, default)=> checkExpr(exp,m,p); in.PatternMatchExp(transformExpr(exp,m,p),typ, cases.map(a=> a match{ case f@in.PatternMatchCaseExp(mExp,exp)=> {checkExpr(exp,m,p); in.PatternMatchCaseExp(handleMPattern(mExp,m,p),transformExpr(exp,m,p))(f.info)} 
                                                                                                                                              case _=>a} ),default match {case Some(exp)=> {checkExpr(exp,m,p); Some(transformExpr(exp,m,p))}case None=>None})(s.info)                                                                                                                                                                             















          
          case s@in.Old(op,typ)=>checkExpr(op,m,p);in.Old(transformExpr(op,m,p),typ)(s.info)
          case s@in.LabeledOld(label, operand)=> checkExpr(operand,m,p); in.LabeledOld(label,transformExpr(operand,m,p))(s.info)
          case s@in.Conditional(cond,thn,els,typ)=> checkExpr(cond,m,p); checkExpr(thn,m,p);checkExpr(els,m,p);in.Conditional(transformExpr(cond,m,p),transformExpr(thn,m,p),transformExpr(els,m,p),typ)(s.info)
          case s@in.FractionalPerm(left,right) => in.FractionalPerm(left,right)(s.info)
          case s@in.Unfolding(a@in.Access(e,pr),ind)=> {checkExpr(pr,m,p);checkExpr(ind,m,p); in.Unfolding(in.Access(transformAccessible(e,m,p),transformExpr(pr,m,p))(a.info),transformExpr(ind,m,p))(s.info)}
          case _=> s}}

        

        def transformAddressable(s:in.Addressable,m:EncodingConfig,p:in.Program):in.Addressable = {s match {
          case s@in.Addressable.Pointer(d@in.Deref(exp,typ))=> checkExpr(exp,m,p); in.Addressable.Pointer(in.Deref(transformExpr(exp,m,p),typ)(d.info))
          case s@in.Addressable.Field(d@in.FieldRef(recv,field))=> checkExpr(recv,m,p); in.Addressable.Field(in.FieldRef(transformExpr(recv,m,p),field)(d.info))
          case s@in.Addressable.Index(d@in.IndexedExp(base,index,typ))=> checkExpr(base,m,p);checkExpr(index,m,p); in.Addressable.Index(in.IndexedExp(transformExpr(base,m,p), transformExpr(index,m,p),typ)(d.info))









        }}

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
              var newMember= in.FPredicate(nameofpredicate, predicate.args, computeNewAssBody(predicate.body,m,p),m)(predicate.info);
                
                methodsToAdd+= newMember; definedFPredicatesDelta+= nameofpredicate->newMember;
             }}
        case s@in.MPredicateAccess(recv,pred,args) => {
         val nameofpredicate = in.MPredicateProxy(pred.name + m.config(), pred.uniqueName + m.config())(pred.info)
           if (p.table.definedMPredicates.contains(nameofpredicate) || definedMPredicatesDelta.contains(nameofpredicate)) {}
           else {
              val predicate= (p.table.lookup(in.MPredicateProxy(pred.name + mpredicatelookup(m, pred, p).config(), pred.uniqueName + mpredicatelookup(m, pred, p).config())(pred.info))).asInstanceOf[in.MPredicate]
              var newMember= in.MPredicate(predicate.receiver, nameofpredicate, predicate.args, computeNewAssBody(predicate.body,m,p),m)(predicate.info);
                
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
              var newMember= in.PureFunction(nameoffunction, function.args, function.results, function.pres, function.posts, function.terminationMeasures, computeNewExprBody(function.body,m,p),m)(function.info);
                
                methodsToAdd+= newMember; definedFunctionsDelta+= nameoffunction->newMember;
                }}

          case s: in.PureMethodCall => {
            val nameofmethod = in.MethodProxy(s.meth.name + m.config(), s.meth.uniqueName + m.config)(s.meth.info)
              if (p.table.definedMethods.contains(nameofmethod) || definedMethodsDelta.contains(nameofmethod)) {}
            else {
              val method= (p.table.lookup(in.MethodProxy(s.meth.name + methodlookup(m, s.meth, p).config(), s.meth.uniqueName + methodlookup(m, s.meth, p).config())(s.meth.info))).asInstanceOf[in.PureMethod]
              var newMember= in.PureMethod(method.receiver, nameofmethod, method.args, method.results, method.pres, method.posts, method.terminationMeasures, computeNewExprBody(method.body,m,p),m)(method.info);
             
               
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
   def computeNewExprBody(body: Option[in.Expr], m:EncodingConfig,p:in.Program): Option[in.Expr] = { body match {
    case Some(a)=> {checkExpr(a,m,p); Some(transformExpr(a,m,p))}
    case None=>None}}
    def computeNewAssBody(body: Option[in.Assertion], m:EncodingConfig,p:in.Program): Option[in.Assertion] = { body match {
    case Some(a)=> { Some(transformAssertion(a,m,p))}
    case None=>None}}
 



  

      


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
      table = p.table.merge(new in.LookupTable(definedMethods = definedMethodsDelta)).merge(new in.LookupTable(definedFunctions = definedFunctionsDelta)).merge(new in.LookupTable(definedMPredicates = definedMPredicatesDelta)).merge(new in.LookupTable(definedFPredicates = definedFPredicatesDelta)),
    )(p.info)
  }
}
