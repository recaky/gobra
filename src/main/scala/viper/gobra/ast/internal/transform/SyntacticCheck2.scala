

package viper.gobra.ast.internal.transform

import viper.gobra.ast.{internal => in}

import viper.gobra.ast.internal.EncodingConfig

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

      def traverseMember(m: in.Member): Unit = {var builtin= false; println (m);println( m.getClass); m match {
        case m:in.DomainDefinition=>{
          val member=m.asInstanceOf[in.DomainDefinition];
            val newMember = in.DomainDefinition(member.name, member.funcs, member.axioms.map(a=> a match{case in.DomainAxiom(exp)=> checkExpr(exp, member.encodingConfig,p);in.DomainAxiom(transformExpr(exp,member.encodingConfig,p))(a.info) case _=>a}))(member.info)
            methodsToAdd+= newMember;
                methodsToRemove+= m;

        }
         case m: in.Method => {
                val member=m.asInstanceOf[in.Method];
                val proxy= in.MethodProxy(member.name.name + member.encodingConfig.config(), member.name.uniqueName + member.encodingConfig.config())(member.name.info)
                val pres= member.pres.map(a=> transformAssertion(a,member.encodingConfig,p))
                val posts=member.posts.map(a=> transformAssertion(a,member.encodingConfig,p))
                val tm= member.terminationMeasures.map(a=>handleTM(a,member.encodingConfig,p))
                val body= member.body.map(a=>computeNewBody(a,member.encodingConfig,p))
                val newMember= in.Method(member.receiver, proxy, member.args, member.results, pres, posts,tm , body, member.encodingConfig )(member.info);
                
                methodsToAdd+= newMember;
                methodsToRemove+= m;
                definedMethodsDelta+= proxy -> newMember
                
                }  
        
        case m: in.Function  => {
             
                val member=m.asInstanceOf[in.Function];
                val proxy= in.FunctionProxy(member.name.name + member.encodingConfig.config())(member.name.info)
                val pres= member.pres.map(a=> transformAssertion(a,member.encodingConfig,p))
                val posts=member.posts.map(a=> transformAssertion(a,member.encodingConfig,p))
                val tm= member.terminationMeasures.map(a=>handleTM(a,member.encodingConfig,p))
                val body= member.body.map(a=>computeNewBody(a,member.encodingConfig,p))
                val newMember= in.Function(proxy, member.args, member.results, pres, posts, tm, body , member.encodingConfig)(member.info)
                methodsToAdd+= newMember;
                methodsToRemove+= m;
                definedFunctionsDelta+= proxy -> newMember}
                
        case m: in.PureFunction => {
                val member=m.asInstanceOf[in.PureFunction];
                val proxy= in.FunctionProxy(member.name.name + member.encodingConfig.config())(member.name.info)
                 val pres= member.pres.map(a=> transformAssertion(a,member.encodingConfig,p))
                val posts=member.posts.map(a=> transformAssertion(a,member.encodingConfig,p))
                val tm= member.terminationMeasures.map(a=>handleTM(a,member.encodingConfig,p))
                val body= computeNewExprBody(member.body,member.encodingConfig,p)
                val newMember= in.PureFunction(proxy, member.args, member.results, pres, posts, tm, body , member.encodingConfig)(member.info);
                methodsToAdd+= newMember;
                methodsToRemove+= m;
                definedFunctionsDelta+= proxy -> newMember
                }
          case m: in.PureMethod => {
                val member=m.asInstanceOf[in.PureMethod];
                val proxy= in.MethodProxy(member.name.name + member.encodingConfig.config(), m.name.uniqueName + member.encodingConfig.config())(member.name.info)
                 val pres= member.pres.map(a=> transformAssertion(a,member.encodingConfig,p))
                val posts=member.posts.map(a=> transformAssertion(a,member.encodingConfig,p))
                val tm= member.terminationMeasures.map(a=>handleTM(a,member.encodingConfig,p))
                val body= computeNewExprBody(member.body,member.encodingConfig,p)
                val newMember= in.PureMethod(member.receiver, proxy, member.args, member.results, pres, posts, tm, body, member.encodingConfig )(member.info);
                
                methodsToAdd+= newMember;
                methodsToRemove+= m;
                definedMethodsDelta+= proxy -> newMember
                
                 }
          case m: in.MPredicate => {
                val member=m.asInstanceOf[in.MPredicate];
                val proxy= in.MPredicateProxy(member.name.name + member.encodingConfig.config(), member.name.uniqueName + member.encodingConfig.config())(member.name.info)
                val body= computeNewAssBody(member.body,member.encodingConfig,p)
                val newMember= in.MPredicate(member.receiver, proxy, member.args, body, member.encodingConfig )(member.info);
                
                methodsToAdd+= newMember;
                methodsToRemove+= m;
                definedMPredicatesDelta+= proxy->newMember
                
                  }
        case m: in.FPredicate => {
                val member=m.asInstanceOf[in.FPredicate];
                val proxy= in.FPredicateProxy(member.name.name + member.encodingConfig.config())(member.name.info)
                val body= computeNewAssBody(member.body,member.encodingConfig,p)
                val newMember= in.FPredicate( proxy, member.args, body, member.encodingConfig )(member.info);
                
                methodsToAdd+= newMember;
                methodsToRemove+= m;
                definedFPredicatesDelta+= proxy->newMember
              
                  }
       case m: in.MethodSubtypeProof => {
              val member = m.asInstanceOf[in.MethodSubtypeProof];
              val proxy = in.MethodProxy(member.subProxy.name + member.encodingConfig.config(), member.subProxy.uniqueName + member.encodingConfig.config())(member.subProxy.info)
              println("proxy=" + proxy)
              val body = member.body match { case Some(block)=> checkStmt(block.asInstanceOf[in.Stmt], member.encodingConfig, p); Some(transformStmt(block.asInstanceOf[in.Stmt], member.encodingConfig,p).asInstanceOf[in.Block]) case None=> None}
              val superT= in.InterfaceT(member.superT.name + member.encodingConfig.config(),member.superT.addressability )
              val proxy2 = in.MethodProxy(member.superProxy.name + member.encodingConfig.config() , member.superProxy.uniqueName + member.encodingConfig.config() )(member.superProxy.info)
              println("proxy2=" + proxy2)
              println(superT);
              val newMember= in.MethodSubtypeProof(member.subProxy, member.superT, member.superProxy, member.receiver, member.args, member.results, body, member.encodingConfig)(member.info)
               methodsToAdd+= newMember;
                methodsToRemove+= m;
                println(newMember);}
          case m: in.PureMethodSubtypeProof => {
              val member = m.asInstanceOf[in.PureMethodSubtypeProof];
              val proxy = in.MethodProxy(member.subProxy.name + member.encodingConfig.config(), member.subProxy.uniqueName + member.encodingConfig.config())(member.subProxy.info)
              println("proxy=" + proxy)
              val body = member.body match { case Some(block)=> checkExpr(block, member.encodingConfig, p); Some(transformExpr(block, member.encodingConfig,p)) case None=> None}
              val superT= in.InterfaceT(member.superT.name + member.encodingConfig.config(),member.superT.addressability )
              val proxy2 = in.MethodProxy(member.superProxy.name + member.encodingConfig.config() , member.superProxy.uniqueName + member.encodingConfig.config() )(member.superProxy.info)
              println("proxy2=" + proxy2)

              val newMember= in.PureMethodSubtypeProof(member.subProxy, member.superT, member.superProxy, member.receiver, member.args, member.results, body, member.encodingConfig)(member.info)
               methodsToAdd+= newMember;
                methodsToRemove+= m;
                println(newMember);}
        
                
                
          case _=>   
                
                
          }
                
        
      
      
      
      }

     def checkStmt(s: in.Stmt, m:EncodingConfig, p: in.Program): Unit = {s match {
      case s: in.FunctionCall => {
        val func= p.table.lookup(s.func)
        if (func.isInstanceOf[in.BuiltInFunction]) {}
          else {
          val nameoffunction = in.FunctionProxy(s.func.name + m.config())(s.func.info)
            if ( definedFunctionsDelta.contains(nameoffunction) || p.table.lookup(s.func).asInstanceOf[in.Function].encodingConfig.config()==m.config()) {}
            else {
              
              val function= p.table.lookup(s.func).asInstanceOf[in.Function]
              
              val newMember= in.Function(nameoffunction, function.args, function.results, function.pres, function.posts, function.terminationMeasures, None,m)(function.info);
              definedFunctionsDelta+= nameoffunction->newMember;
              val pres= function.pres.map(a=> transformAssertion(a,m,p))
              val posts= function.posts.map(a=> transformAssertion(a,m,p))
              val tm= function.terminationMeasures.map(a=>handleTM(a,m,p))
              val newMember2= in.Function(nameoffunction, function.args, function.results, pres, posts, tm, None,m)(function.info);


                
                methodsToAdd+= newMember2; definedFunctionsDelta+= nameoffunction->newMember2;
                }}}
      case s: in.GoFunctionCall => {
         val func= p.table.lookup(s.func)
        if (func.isInstanceOf[in.BuiltInFunction]) {}
        else if (func.isInstanceOf[in.PureFunction]) {
               val nameoffunction = in.FunctionProxy(s.func.name + m.config())(s.func.info)
          
            if ( definedFunctionsDelta.contains(nameoffunction)|| p.table.lookup(s.func).asInstanceOf[in.PureFunction].encodingConfig.config()==m.config()) {}
            else {
             
              val function= (p.table.lookup(s.func)).asInstanceOf[in.PureFunction]
              val newMember= in.PureFunction(nameoffunction, function.args, function.results, function.pres, function.posts, function.terminationMeasures, None,m)(function.info);
              definedFunctionsDelta+= nameoffunction->newMember;
              val pres= function.pres.map(a=> transformAssertion(a,m,p))
              val posts= function.posts.map(a=> transformAssertion(a,m,p))
              val tm= function.terminationMeasures.map(a=>handleTM(a,m,p))
              val newMember2= in.PureFunction(nameoffunction, function.args, function.results, pres, posts, tm, computeNewExprBody(function.body,m,p),m)(function.info);
        
              methodsToAdd+= newMember2; definedFunctionsDelta+= nameoffunction->newMember2;
                } }
        else {
          val nameoffunction = in.FunctionProxy(s.func.name + m.config())(s.func.info)
          
            if ( definedFunctionsDelta.contains(nameoffunction)|| p.table.lookup(s.func).asInstanceOf[in.Function].encodingConfig.config()==m.config()) {}
            else {
             
              val function= (p.table.lookup(s.func)).asInstanceOf[in.Function]
              val newMember= in.Function(nameoffunction, function.args, function.results, function.pres, function.posts, function.terminationMeasures, None,m)(function.info);
              definedFunctionsDelta+= nameoffunction->newMember;
              val pres= function.pres.map(a=> transformAssertion(a,m,p))
              val posts= function.posts.map(a=> transformAssertion(a,m,p))
              val tm= function.terminationMeasures.map(a=>handleTM(a,m,p))
              val newMember2= in.Function(nameoffunction, function.args, function.results, pres, posts, tm, None,m)(function.info);

                methodsToAdd+= newMember2; definedFunctionsDelta+= nameoffunction->newMember2;
                }}}
                
      case s: in.MethodCall => {
        val met=p.table.lookup(s.meth)
        
       if (met.isInstanceOf[in.BuiltInMethod]) {}
        else {
            val nameofmethod = in.MethodProxy(s.meth.name + m.config(), s.meth.uniqueName + m.config())(s.meth.info)
              if ( definedMethodsDelta.contains(nameofmethod) || p.table.lookup(s.meth).asInstanceOf[in.Method].encodingConfig.config()==m.config()) {}
            else {
              val method= p.table.lookup(s.meth).asInstanceOf[in.Method]
              
              val newMember= in.Method(method.receiver, nameofmethod, method.args, method.results, method.pres,method.posts , method.terminationMeasures, None,m)(method.info);
              definedMethodsDelta+= nameofmethod->newMember;
              val pres= method.pres.map(a=> transformAssertion(a,m,p))
              val posts= method.posts.map(a=> transformAssertion(a,m,p))
              val tm= method.terminationMeasures.map(a=>handleTM(a,m,p))
              val newMember2= in.Method(method.receiver, nameofmethod, method.args, method.results, pres,posts , tm, None,m)(method.info);
              methodsToAdd+= newMember2; definedMethodsDelta+= nameofmethod->newMember2;
                }}}
      case s: in.GoMethodCall => {
        val met=p.table.lookup(s.meth)
        if (met.isInstanceOf[in.BuiltInMethod]) {}
        else if (met.isInstanceOf[in.PureMethod]){
            val nameofmethod = in.MethodProxy(s.meth.name + m.config(), s.meth.uniqueName + m.config())(s.meth.info)
              if ( definedMethodsDelta.contains(nameofmethod)|| p.table.lookup(s.meth).asInstanceOf[in.PureMethod].encodingConfig.config()==m.config()) {}
            else {
              val method= p.table.lookup(s.meth).asInstanceOf[in.PureMethod]
              
              
              val newMember= in.PureMethod(method.receiver, nameofmethod, method.args, method.results, method.pres, method.posts, method.terminationMeasures, None,m)(method.info);
              definedMethodsDelta+= nameofmethod->newMember;
              val pres= method.pres.map(a=> transformAssertion(a,m,p))
              val posts= method.posts.map(a=> transformAssertion(a,m,p))
              val tm= method.terminationMeasures.map(a=>handleTM(a,m,p))
               
               val newMember2= in.PureMethod(method.receiver, nameofmethod, method.args, method.results, pres, posts, tm, computeNewExprBody(method.body,m,p),m)(method.info);
                methodsToAdd+= newMember2; definedMethodsDelta+= nameofmethod->newMember2;
                }




        }
        else {
            val nameofmethod = in.MethodProxy(s.meth.name + m.config(), s.meth.uniqueName + m.config())(s.meth.info)
              if ( definedMethodsDelta.contains(nameofmethod)|| p.table.lookup(s.meth).asInstanceOf[in.Method].encodingConfig.config()==m.config()) {}
            else {
              val method= p.table.lookup(s.meth).asInstanceOf[in.Method]
            
              val newMember= in.Method(method.receiver, nameofmethod, method.args, method.results, method.pres, method.posts, method.terminationMeasures, None,m)(method.info);
              definedMethodsDelta+= nameofmethod->newMember;
              val pres= method.pres.map(a=> transformAssertion(a,m,p))
              val posts= method.posts.map(a=> transformAssertion(a,m,p))
              val tm= method.terminationMeasures.map(a=>handleTM(a,m,p))
              val newMember2= in.Method(method.receiver, nameofmethod, method.args, method.results, pres, posts, tm, None,m)(method.info);
              
                methodsToAdd+= newMember2; definedMethodsDelta+= nameofmethod->newMember2;
                }}}
      

      
       case _=>
                
        
      }}
      def handleAssignee(s:in.Assignee, m:EncodingConfig,p:in.Program):in.Assignee= s match {
        case in.Assignee.Pointer(d@in.Deref(exp,typ))=> checkExpr(exp,m,p); in.Assignee.Pointer(in.Deref(transformExpr(exp,m,p),typ)(d.info))
        case in.Assignee.Field(d@in.FieldRef(recv,field))=> checkExpr(recv,m,p); in.Assignee.Field(in.FieldRef(transformExpr(recv,m,p),field)(d.info))
        case in.Assignee.Index(d@in.IndexedExp(base,index,typ))=> checkExpr(base,m,p);checkExpr(index,m,p); in.Assignee.Index(in.IndexedExp(transformExpr(base,m,p),transformExpr(index,m,p),typ)(d.info))
        case _=> s

      }
     
      def transformStmt(s: in.Stmt, m:EncodingConfig,p:in.Program):in.Stmt= {s match {
          case d@in.Defer(stmt)=> checkStmt(stmt,m,p); in.Defer(transformStmt(stmt,m,p).asInstanceOf[in.Deferrable])(d.info)
          case s@in.SingleAss(l,r)=>{checkExpr(r,m,p);in.SingleAss(handleAssignee(l,m,p),transformExpr(r,m,p))(s.info)}
          case s@in.Block(decls,stmts) => stmts.map(a=> checkStmt(a,m,p));in.Block(decls,stmts.map(a=> transformStmt(a,m,p)))(s.info)
          case s@in.Seqn(stmts) => stmts.map(a=> checkStmt(a,m,p)); in.Seqn(stmts.map(a=> transformStmt(a,m,p)))(s.info)
          case i@in.If(cond, thn, els) => checkExpr(cond,m,p);checkStmt(thn,m,p); checkStmt(els,m,p);in.If(transformExpr(cond,m,p), transformStmt(thn,m,p),transformStmt(els,m,p))(i.info)
          case w@in.While(cond, invs, terminationMeasure, body) =>checkExpr(cond,m,p);checkStmt(body,m,p);in.While(transformExpr(cond,m,p),invs.map(a=>transformAssertion(a,m,p)), terminationMeasure match { case Some(tm)=> Some(handleTM(tm,m,p)) case None=>None}, transformStmt(body,m,p))(w.info)
          case s@in.SafeMapLookup(res,succ,d@in.IndexedExp(base,ind,typ))=>{checkExpr(base,m,p);checkExpr(ind,m,p);in.SafeMapLookup(res,succ,in.IndexedExp(transformExpr(base,m,p),transformExpr(ind,m,p),typ)(d.info))(s.info)}
          case s@in.FunctionCall(targets,func,args) => if (p.table.lookup(func).isInstanceOf[in.BuiltInFunction]){s}else {  val nameoffunction = in.FunctionProxy(func.name + m.config())(func.info); in.FunctionCall (targets, nameoffunction,args.map(a=> {checkExpr(a,m,p);transformExpr(a,m,p)}))(s.info); }
          case s@in.GoFunctionCall(func, args) => if (p.table.lookup(func).isInstanceOf[in.BuiltInFunction]){s}else  {val nameoffunction = in.FunctionProxy(func.name + m.config())(func.info); in.GoFunctionCall ( nameoffunction,args.map(a=> {checkExpr(a,m,p);transformExpr(a,m,p)}))(s.info); }
          case s@in.MethodCall(targets, recv, meth, args) => if (p.table.lookup(meth).isInstanceOf[in.BuiltInMethod]){s} else { val nameofmethod = in.MethodProxy(meth.name + m.config(), meth.uniqueName+ m.config())(meth.info); in.MethodCall (targets,recv, nameofmethod,args.map(a=> {checkExpr(a,m,p);transformExpr(a,m,p)}))(s.info);}
          case s@in.GoMethodCall(recv,meth, args) => if (p.table.lookup(meth).isInstanceOf[in.BuiltInMethod]){s} else {val nameofmethod = in.MethodProxy(meth.name + m.config(), meth.uniqueName+ m.config())(meth.info); in.GoMethodCall (recv, nameofmethod,args.map(a=> {checkExpr(a,m,p);transformExpr(a,m,p)}))(s.info); }
          case s@in.Inhale(ass)=>in.Inhale(transformAssertion(ass,m,p))(s.info)
          case s@in.Exhale(ass)=>in.Exhale(transformAssertion(ass,m,p))(s.info)
          case s@in.Assert(ass)=>in.Assert(transformAssertion(ass,m,p))(s.info)
          case s@in.Assume(ass)=>in.Assume(transformAssertion(ass,m,p))(s.info)
          case s@in.Fold(a@in.Access(e,pr))=>{checkExpr(pr,m,p);in.Fold(in.Access(transformAccessible(e,m,p),transformExpr(pr,m,p))(a.info))(s.info)}
          case s@in.Unfold(a@in.Access(e,pr))=>{checkExpr(pr,m,p);in.Unfold(in.Access(transformAccessible(e,m,p),transformExpr(pr,m,p))(a.info))(s.info)}
          case s@in.MakeMap(target,typeParam,init)=> {in.MakeMap(target,typeParam,init match {case Some(a)=>checkExpr(a,m,p);Some(transformExpr(a,m,p)) case None=> None})(s.info)}
          case s@in.MakeSlice(target,typeParam,lenArg,capArg)=> {checkExpr(lenArg,m,p);in.MakeSlice(target,typeParam,transformExpr(lenArg,m,p),capArg match {case Some(a)=>checkExpr(a,m,p);Some(transformExpr(a,m,p)) case None=> None})(s.info)}
          case s@in.New(target,expr)=>{checkExpr(expr,m,p); in.New(target,transformExpr(expr,m,p))(s.info)}
          case s@in.Outline(name,pres,posts,tm,body,trusted)=> {checkStmt(body,m,p);in.Outline(name,pres.map(a=> transformAssertion(a,m,p)),posts.map(a=> transformAssertion(a,m,p)),tm.map(a=>handleTM(a,m,p)),transformStmt(body,m,p),trusted)(s.info)}
          case s@in.SafeTypeAssertion(res,succ,expr,typ)=>{checkExpr(expr,m,p);in.SafeTypeAssertion(res,succ,transformExpr(expr,m,p),typ)(s.info) }
          case s@in.EffectfulConversion(target,newType, expr)=> checkExpr(expr,m,p); in.EffectfulConversion(target,newType,transformExpr(expr,m,p))(s.info)
          case s@in.PackageWand(d@in.MagicWand(left,right), block)=> in.PackageWand(in.MagicWand(transformAssertion(left,m,p), transformAssertion(right,m,p))(d.info), (block match {case Some(a)=>checkStmt(a,m,p); Some(transformStmt(a,m,p))       case None=> None        }))(s.info)
          case s@in.NewMapLit(target,keys,values,entries)=>in.NewMapLit(target,keys,values,entries.map(a=> a match { case (a,b)=>({checkExpr(a,m,p);transformExpr(a,m,p)},{checkExpr(a,m,p);transformExpr(b,m,p)})}))(s.info) 
          case s@in.NewSliceLit(target,mem,elems)=>in.NewSliceLit(target,mem,elems.view.mapValues(a=>{checkExpr(a,m,p);transformExpr(a,m,p)}).toMap)(s.info)
                                                                                                                                                                                
          case s@in.ApplyWand(d@in.MagicWand(left,right))=>in.ApplyWand(in.MagicWand(transformAssertion(left,m,p), transformAssertion(right,m,p))(d.info))(s.info) 
          case s@in.PatternMatchStmt(exp, cases, strict)=> checkExpr(exp,m,p); in.PatternMatchStmt(transformExpr(exp,m,p), cases.map(a=> a match{ case f@in.PatternMatchCaseStmt(mExp,body)=> {checkStmt(body,m,p); in.PatternMatchCaseStmt(handleMPattern(mExp,m,p),transformStmt(body,m,p))(f.info)} 
                                                                                                                                   case _=>a} ),strict)(s.info)  
          case s@in.PredExprFold(d@in.PredicateConstructor(proxy,proxyT,arg),args,pi)=> args.map(a=>checkExpr(a,m,p));checkExpr(pi,m,p); in.PredExprFold(in.PredicateConstructor(handleProxy(proxy,m,p),proxyT,arg.map(a=> a match {case Some(ex)=>{checkExpr(ex,m,p);Some(transformExpr(ex,m,p))}case None=>None}))(d.info),args.map(a=> transformExpr(a,m,p)),transformExpr(pi,m,p))(s.info)                                                                                                                                                                        
          case s@in.PredExprUnfold(d@in.PredicateConstructor(proxy,proxyT,arg),args,pi)=> args.map(a=>checkExpr(a,m,p));checkExpr(pi,m,p); in.PredExprUnfold(in.PredicateConstructor(handleProxy(proxy,m,p),proxyT,arg.map(a=> a match {case Some(ex)=>{checkExpr(ex,m,p);Some(transformExpr(ex,m,p))}case None=>None}))(d.info),args.map(a=> transformExpr(a,m,p)),transformExpr(pi,m,p))(s.info)                                                                                                                                                                        
          case _=> s





      }}
       def handleProxy(s:in.PredicateProxy, m:EncodingConfig, p:in.Program):in.PredicateProxy= {s match{
          case s@in.FPredicateProxy(name)=> {
            if (p.table.lookup(s).isInstanceOf[in.BuiltInFPredicate]) {s}
            else {
            val nameofpredicate = in.FPredicateProxy(name + m.config())(s.info)
           if ( definedFPredicatesDelta.contains(nameofpredicate) || p.table.lookup(s).asInstanceOf[in.FPredicate].encodingConfig.config()==m.config()) {in.FPredicateProxy(name + m.config())(s.info)}
           else {
              val predicate= p.table.lookup(s).asInstanceOf[in.FPredicate]
            
              val newMember= in.FPredicate(nameofpredicate, predicate.args, None,m)(predicate.info);
              definedFPredicatesDelta+= nameofpredicate->newMember;
              val newMember2 = in.FPredicate (nameofpredicate, predicate.args, computeNewAssBody(predicate.body,m,p),m)(predicate.info)

                
                methodsToAdd+= newMember2;
                definedFPredicatesDelta+= nameofpredicate->newMember2;
            in.FPredicateProxy(name + m.config())(s.info)}}}
          case s@in.MPredicateProxy(name, uniqueName)=> {
            if (p.table.lookup(s).isInstanceOf[in.BuiltInMPredicate]) {s}
            else {
            
            val nameofpredicate = in.MPredicateProxy(name + m.config(),uniqueName + m.config())(s.info)
           if ( definedMPredicatesDelta.contains(nameofpredicate)|| p.table.lookup(s).asInstanceOf[in.MPredicate].encodingConfig.config()==m.config()) {in.MPredicateProxy(name+ m.config(), uniqueName + m.config())(s.info)}
           else {
              val predicate= (p.table.lookup(s)).asInstanceOf[in.MPredicate]
              
              val newMember= in.MPredicate(predicate.receiver, nameofpredicate, predicate.args,None ,m)(predicate.info);
              definedMPredicatesDelta+= nameofpredicate->newMember;
              val newMember2= in.MPredicate(predicate.receiver, nameofpredicate, predicate.args, computeNewAssBody(predicate.body,m,p),m)(predicate.info)
                
                methodsToAdd+= newMember2;   definedMPredicatesDelta+= nameofpredicate->newMember2;
            in.MPredicateProxy(name+ m.config(), uniqueName + m.config())(s.info)}}}
          case _=> s




       }}
        

       def handleMPattern(s:in.MatchPattern, m:EncodingConfig, p:in.Program): in.MatchPattern= {s match {
    case s@in.MatchValue(exp)=> checkExpr(exp,m,p); in.MatchValue(transformExpr(exp,m,p))(s.info)
    case s@in.MatchAdt(clause,expr)=>  in.MatchAdt(clause,expr.map(a=> handleMPattern(a,m,p)))(s.info)
    case _=> s}}
    
     
     
     def handleTM(s:in.TerminationMeasure,m:EncodingConfig,p:in.Program):in.TerminationMeasure= s match{
     case s@in.WildcardMeasure(cond)=> in.WildcardMeasure(cond match {case Some(exp)=>checkExpr(exp,m,p); Some(transformExpr(exp,m,p)) case None=>None})(s.info)
     case s@in.TupleTerminationMeasure(tuple,cond)=>in.TupleTerminationMeasure((tuple.map(node=>(if (node.isInstanceOf[in.Expr]){checkExpr(node.asInstanceOf[in.Expr],m,p);transformExpr(node.asInstanceOf[in.Expr],m,p)}else {checkPredAccess(node.asInstanceOf[in.PredicateAccess],m,p);transformPredAccess(node.asInstanceOf[in.PredicateAccess],m,p)}))),cond match {case Some(exp)=>checkExpr(exp,m,p); Some(transformExpr(exp,m,p))case None=> None})(s.info)
      case _=>s
}
        def transformExpr(s:in.Expr, m:EncodingConfig,p:in.Program):in.Expr= {s match {
          case s@in.SequenceLit(length,mem,elems)=> in.SequenceLit(length,mem,elems.view.mapValues(a=> {checkExpr(a,m,p);transformExpr(a,m,p)}).toMap)(s.info)
          case s@in.Let(left,right,ind)=> checkExpr(right,m,p);checkExpr(ind,m,p);in.Let(left,transformExpr(right,m,p),transformExpr(ind,m,p))(s.info)  
          case s@in.PureFunctionCall(func,args,typ) => {val nameoffunction = in.FunctionProxy(func.name + m.config())(func.info); in.PureFunctionCall (nameoffunction,args.map(a=> {checkExpr(a,m,p);transformExpr(a,m,p)}),typ)(s.info);}
          case s@in.PureMethodCall(recv,meth,args,typ) => {val nameofmethod = in.MethodProxy(meth.name + m.config(), meth.uniqueName + m.config())(meth.info); in.PureMethodCall (recv,nameofmethod,args.map(a=> {checkExpr(a,m,p);transformExpr(a,m,p)}),typ)(s.info);}
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
          case s@in.SetLit(mem,exprs)=> exprs.map(a=> checkExpr(a,m,p)); in.SetLit(mem,exprs.map(a=>transformExpr(a,m,p)))(s.info)
          case s@in.SetConversion(exp)=> checkExpr(exp,m,p);in.SetConversion(transformExpr(exp,m,p))(s.info)
          case s@in.MultisetLit(mem,exprs)=> exprs.map(a=> checkExpr(a,m,p)); in.MultisetLit(mem,exprs.map(a=>transformExpr(a,m,p)))(s.info)
          case s@in.MultisetConversion(exp)=> checkExpr(exp,m,p);in.MultisetConversion(transformExpr(exp,m,p))(s.info)
          case s@in.MathMapLit(keys,values,entries)=>in.MathMapLit(keys,values, entries.map(a=> a match {case (a,b)=>{checkExpr(a,m,p);checkExpr(b,m,p);(transformExpr(a,m,p),transformExpr(b,m,p))}}))(s.info)
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
          case s@in.StructLit(typ,args)=>args.map(a=> checkExpr(a,m,p)); in.StructLit(typ,args.map(a=> transformExpr(a,m,p)))(s.info)
          
          case s@in.ArrayLit(length,mem,elems)=>in.ArrayLit(length,mem,elems.view.mapValues(a=>{checkExpr(a,m,p);transformExpr(a,m,p)}).toMap)(s.info)
          case s@in.AdtConstructorLit(typ,clause,args)=> in.AdtConstructorLit(typ,clause,args.map(a=> {checkExpr(a,m,p);transformExpr(a,m,p)}))(s.info)

          case s@in.PureForall(vars,triggers,body)=>checkExpr(body,m,p); in.PureForall(vars, triggers.map(a=> handleTrigger(a,m,p)), transformExpr(body,m,p))(s.info)
          case s@in.Exists(vars,triggers,body)=>checkExpr(body,m,p); in.Exists(vars, triggers.map(a=> handleTrigger(a,m,p)), transformExpr(body,m,p))(s.info)
          case in.Old(op,typ)=>checkExpr(op,m,p);in.Old(transformExpr(op,m,p),typ)(s.info)
          case in.LabeledOld(label, operand)=> checkExpr(operand,m,p); in.LabeledOld(label,transformExpr(operand,m,p))(s.info)
          case in.Conditional(cond,thn,els,typ)=> checkExpr(cond,m,p); checkExpr(thn,m,p);checkExpr(els,m,p);in.Conditional(transformExpr(cond,m,p),transformExpr(thn,m,p),transformExpr(els,m,p),typ)(s.info)
          case in.FractionalPerm(left,right)=>{checkExpr(left,m,p);checkExpr(right,m,p); in.FractionalPerm(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)}
          
          case in.Unfolding(a@in.Access(e,pr),ind)=> {checkExpr(pr,m,p);checkExpr(ind,m,p); in.Unfolding(in.Access(transformAccessible(e,m,p),transformExpr(pr,m,p))(a.info),transformExpr(ind,m,p))(s.info)}
          case in.CurrentPerm(in.Accessible.Predicate(op))=>checkPredAccess(op,m,p);in.CurrentPerm(in.Accessible.Predicate(transformPredAccess(op,m,p)))(s.info)
          case in.PermMinus(exp)=>checkExpr(exp,m,p); in.PermMinus(transformExpr(exp,m,p))(s.info)

          case in.PermAdd(left,right)=>checkExpr(left,m,p);checkExpr(right,m,p); in.PermAdd(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case in.PermSub(left,right)=>checkExpr(left,m,p);checkExpr(right,m,p); in.PermSub(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case in.PermMul(left,right)=>checkExpr(left,m,p);checkExpr(right,m,p); in.PermMul(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case in.PermDiv(left,right)=>checkExpr(left,m,p);checkExpr(right,m,p); in.PermDiv(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case in.PermLtCmp(left,right)=>checkExpr(left,m,p);checkExpr(right,m,p); in.PermLtCmp(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case in.PermLeCmp(left,right)=>checkExpr(left,m,p);checkExpr(right,m,p); in.PermLeCmp(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case in.PermGtCmp(left,right)=>checkExpr(left,m,p);checkExpr(right,m,p); in.PermGtCmp(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)
          case in.PermGeCmp(left,right)=>checkExpr(left,m,p);checkExpr(right,m,p); in.PermGeCmp(transformExpr(left,m,p),transformExpr(right,m,p))(s.info)


          case _=> s}}

        

        def transformAddressable(s:in.Addressable,m:EncodingConfig,p:in.Program):in.Addressable = {s match {
          case in.Addressable.Pointer(d@in.Deref(exp,typ))=> checkExpr(exp,m,p); in.Addressable.Pointer(in.Deref(transformExpr(exp,m,p),typ)(d.info))
          case in.Addressable.Field(d@in.FieldRef(recv,field))=> checkExpr(recv,m,p); in.Addressable.Field(in.FieldRef(transformExpr(recv,m,p),field)(d.info))
          case in.Addressable.Index(d@in.IndexedExp(base,index,typ))=> checkExpr(base,m,p);checkExpr(index,m,p); in.Addressable.Index(in.IndexedExp(transformExpr(base,m,p), transformExpr(index,m,p),typ)(d.info))
          case _=> s}}
        def handleTriggerExpr(s:in.TriggerExpr,m:EncodingConfig,p:in.Program): in.TriggerExpr= s match {
            case in.Accessible.Predicate(op)=> checkPredAccess(op,m,p); in.Accessible.Predicate(transformPredAccess(op,m,p))
            case _=> checkExpr(s.asInstanceOf[in.Expr],m,p);transformExpr(s.asInstanceOf[in.Expr],m,p)}
        def handleTrigger(s:in.Trigger,m:EncodingConfig, p:in.Program):in.Trigger= s match {
            case s@in.Trigger(exprs)=>in.Trigger(exprs.map(a=> handleTriggerExpr(a,m,p)))(s.info)
            case _=>s
}




        

        def transformAssertion (s:in.Assertion,m:EncodingConfig,p:in.Program):in.Assertion= { s match {
          case s@in.SepForall(vars,triggers,body)=> in.SepForall(vars,triggers.map(a=> handleTrigger(a,m,p)),transformAssertion(body,m,p))(s.info)
          case s@in.SepAnd(left, right)=> in.SepAnd(transformAssertion(left,m,p),transformAssertion(right,m,p))(s.info)
          case s@in.ExprAssertion(exp)=> {checkExpr(exp,m,p);in.ExprAssertion(transformExpr(exp,m,p))(s.info)}
          case s@in.Implication(left,right) => {checkExpr(left,m,p);in.Implication(transformExpr(left,m,p),transformAssertion(right,m,p))(s.info) }
          case s@in.Access(e,pr)=> {checkExpr(pr,m,p); in.Access(transformAccessible(e,m,p),transformExpr(pr,m,p))(s.info)}
          case s@in.MagicWand(left,right)=>in.MagicWand(transformAssertion(left,m,p),transformAssertion(right,m,p))(s.info)
          case _=> s
          }}

        
        def transformAccessible(s:in.Accessible,m:EncodingConfig, p:in.Program):in.Accessible = {
          s match {
           case in.Accessible.ExprAccess(op)=>{ checkExpr(op,m,p); in.Accessible.ExprAccess(transformExpr(op,m,p))}
           case in.Accessible.Predicate(op)=> {checkPredAccess(op,m,p);in.Accessible.Predicate(transformPredAccess(op,m,p))}
           case in.Accessible.PredExpr(pred@in.PredExprInstance(base,args))=>{checkExpr(base,m,p);args.map(a=> checkExpr(a,m,p));in.Accessible.PredExpr(in.PredExprInstance(transformExpr(base,m,p), args.map(a=>transformExpr(a,m,p)))(pred.info))}
           case _=> s






        }
   }
        def checkPredAccess(s:in.PredicateAccess,m:EncodingConfig,p:in.Program):Unit= {s match{
         case in.FPredicateAccess(pred,_) => {
          if (p.table.lookup(pred).isInstanceOf[in.BuiltInFPredicate]) {}
          else {
         val nameofpredicate = in.FPredicateProxy(pred.name + m.config())(pred.info)
          if ( definedFPredicatesDelta.contains(nameofpredicate) || p.table.lookup(pred).asInstanceOf[in.FPredicate].encodingConfig.config()==m.config()) {}
          else {
              val predicate= p.table.lookup(pred).asInstanceOf[in.FPredicate]
              val newMember= in.FPredicate(nameofpredicate, predicate.args, None,m)(predicate.info);
              definedFPredicatesDelta+= nameofpredicate->newMember;

              val newMember2 = in.FPredicate(nameofpredicate, predicate.args, computeNewAssBody(predicate.body,m,p),m)(predicate.info);
              definedFPredicatesDelta+= nameofpredicate-> newMember2;
              methodsToAdd += newMember2
              
             }
            }}
        case in.MPredicateAccess(_,pred,_) => {
          if (p.table.lookup(pred).isInstanceOf[in.BuiltInMPredicate]) {}
          else {
         val nameofpredicate = in.MPredicateProxy(pred.name + m.config(), pred.uniqueName + m.config())(pred.info)
           if ( definedMPredicatesDelta.contains(nameofpredicate)|| p.table.lookup(pred).asInstanceOf[in.MPredicate].encodingConfig.config()==m.config()) {}
           else {
              val predicate= (p.table.lookup(pred)).asInstanceOf[in.MPredicate]
              val newMember= in.MPredicate(predicate.receiver, nameofpredicate, predicate.args, None,m)(predicate.info);
            definedMPredicatesDelta+= nameofpredicate->newMember;
            val newMember2 = in.MPredicate(predicate.receiver, nameofpredicate, predicate.args, computeNewAssBody(predicate.body,m,p),m)(predicate.info);
            definedMPredicatesDelta+= nameofpredicate-> newMember2;
              methodsToAdd += newMember2

             }
             }}

        case _ =>

      


       }}
       def transformPredAccess (s:in.PredicateAccess, m:EncodingConfig,p:in.Program):in.PredicateAccess= {s match {
          case s@in.FPredicateAccess(pred,args)=> {args.map(a=>checkExpr(a,m,p));if (p.table.lookup(pred).isInstanceOf[in.BuiltInFPredicate]){s} else {val name= in.FPredicateProxy(pred.name + m.config())(pred.info); in.FPredicateAccess(name, args.map(a=> transformExpr(a,m,p)))(s.info)}}
          case s@in.MPredicateAccess(recv,pred,args)=> {args.map(a=>checkExpr(a,m,p)); if (p.table.lookup(pred).isInstanceOf[in.BuiltInMPredicate]) {s} else {val name= in.MPredicateProxy(pred.name + m.config(),pred.uniqueName + m.config())(pred.info); in.MPredicateAccess(recv, name, args.map(a=> transformExpr(a,m,p)))(s.info)}}
          case s@in.MemoryPredicateAccess(arg)=>{checkExpr(arg,m,p);in.MemoryPredicateAccess(transformExpr(arg,m,p))(s.info)
        }
           case _ => s





        }} 
        def checkExpr (s:in.Expr, m:EncodingConfig, p:in.Program):Unit= { s match {
          case s: in.PureFunctionCall => {  val nameoffunction = in.FunctionProxy(s.func.name + m.config())(s.func.info)
            if (definedFunctionsDelta.contains(nameoffunction)|| p.table.lookup(s.func).asInstanceOf[in.PureFunction].encodingConfig.config()==m.config()) {}
            else {
              val function= (p.table.lookup(s.func)).asInstanceOf[in.PureFunction]
              val newMember= in.PureFunction(nameoffunction, function.args, function.results, function.pres, function.posts, function.terminationMeasures, None,m)(function.info);
              definedFunctionsDelta+= nameoffunction->newMember;
              val pres= function.pres.map(a=> transformAssertion(a,m,p))
              val posts= function.posts.map(a=> transformAssertion(a,m,p))
              val tm= function.terminationMeasures.map(a=>handleTM(a,m,p))
              val newMember2= in.PureFunction(nameoffunction, function.args, function.results, pres, posts, tm, computeNewExprBody(function.body,m,p),m)(function.info);
              methodsToAdd+= newMember2; definedFunctionsDelta+= nameoffunction->newMember2;
                }}

          case s: in.PureMethodCall => {
            val nameofmethod = in.MethodProxy(s.meth.name + m.config(), s.meth.uniqueName + m.config())(s.meth.info)
              if ( definedMethodsDelta.contains(nameofmethod) || p.table.lookup(s.meth).asInstanceOf[in.PureMethod].encodingConfig.config()==m.config()) {}
            else {
              val method= (p.table.lookup(s.meth)).asInstanceOf[in.PureMethod]
              
             
              val newMember= in.PureMethod(method.receiver, nameofmethod, method.args, method.results, method.pres, method.posts,method.terminationMeasures, None,m)(method.info);
              definedMethodsDelta+= nameofmethod->newMember;
              val pres= method.pres.map(a=> transformAssertion(a,m,p))
              val posts= method.posts.map(a=> transformAssertion(a,m,p))
              val tm= method.terminationMeasures.map(a=>handleTM(a,m,p))
              val newMember2 = in.PureMethod(method.receiver, nameofmethod, method.args, method.results, pres, posts,tm,  computeNewExprBody(method.body,m,p),m)(method.info);
              methodsToAdd+= newMember2; definedMethodsDelta+= nameofmethod->newMember2;
                }}
      
          case _=>



        }}



     def computeNewBody(body: in.MethodBody, m:EncodingConfig,p:in.Program): in.MethodBody = {
    in.MethodBody(
      body.decls,
      in.MethodBodySeqn(body.seqn.stmts.map (a=> {checkStmt(a,m,p);transformStmt(a,m,p)}))(body.seqn.info),
      body.postprocessing.map (a=> {checkStmt(a,m,p);transformStmt(a,m,p)}),
    )(body.info)
  }
   def computeNewExprBody(body: Option[in.Expr], m:EncodingConfig,p:in.Program): Option[in.Expr] = { body match {
    case Some(a)=> {checkExpr(a,m,p); Some(transformExpr(a,m,p))}
    case None=>None}}
    def computeNewAssBody(body: Option[in.Assertion], m:EncodingConfig,p:in.Program): Option[in.Assertion] = { body match {
    case Some(a)=> { Some(transformAssertion(a,m,p))}
    case None=>None}}
      

      members.foreach(traverseMember);
  
    in.Program(
      types = p.types,
      members = p.members.diff(methodsToRemove.toSeq).appendedAll(methodsToAdd),
      table = p.table.merge(new in.LookupTable(definedMethods = definedMethodsDelta)).merge(new in.LookupTable(definedFunctions = definedFunctionsDelta)).merge(new in.LookupTable(definedMPredicates = definedMPredicatesDelta)).merge(new in.LookupTable(definedFPredicates = definedFPredicatesDelta)),
    )(p.info)
  }
}
