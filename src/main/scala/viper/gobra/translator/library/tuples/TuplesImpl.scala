// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.
package viper.gobra.translator.library.tuples
import scala.language.postfixOps

import viper.gobra.translator.Names
import viper.silver.{ast => vpr}
import viper.gobra.translator.util.ViperUtil.synthesized

import scala.collection.mutable
import viper.silver.plugin.standard.termination

class TuplesImpl extends Tuples {

  /**
    * Finalizes translation. `addMemberFn` is called with any member that is part of the encoding.
    */
  override def finalize(addMemberFn: vpr.Member => Unit): Unit = {
    generatedDomains.take(2) foreach addMemberFn
  }

  override def typ(args: Vector[vpr.Type]): vpr.DomainType = {
  vpr.DomainType(
      domain = vpr.Domain(name="Struct", typVars= Nil, functions = Seq(vpr.DomainFunc(s"struct_loc", Seq( vpr.LocalVarDecl("s",vpr.TypeVar(s"Struct"))(),vpr.LocalVarDecl("m",vpr.Int)()), vpr.Int)(domainName = "Struct")),
    axioms=Nil
    
    )(),
      typVarsMap = Map.empty
    )
  }

  

  override def create(args: Vector[vpr.Exp])(pos: vpr.Position, info: vpr.Info, errT: vpr.ErrorTrafo): vpr.DomainFuncApp = {
    addNTuplesDomain(0);
    val domainName= "Struct"
    val domainType = vpr.DomainType (domainName, Map (vpr.TypeVar(s"Struct")->vpr.TypeVar(s"Struct")))(Seq.empty)
    println(args)
    val arity = args.size
    
    
  
    if (arity==0) { vpr.DomainFuncApp(
      funcname = "default_tuple",
      args = Seq(vpr.IntLit(0)()),
      typVarMap = Map.empty
    )(vpr.NoPosition,vpr.NoInfo, domainType, s"StructOps",vpr.NoTrafos)}


    else helper(args, args.size)(pos,info,errT)
  }
  def helper (args: Vector[vpr.Exp], fields:Int)(pos: vpr.Position, info: vpr.Info, errT: vpr.ErrorTrafo): vpr.DomainFuncApp = {
    val domainName= "Struct"
    val domainName2= "ShStruct"
    val domainType = vpr.DomainType (domainName, Map (vpr.TypeVar(s"Struct")->vpr.TypeVar(s"Struct")))(Seq.empty)
    val arity = args.size
    val index = arity - 1
    val value = if (!args.isEmpty) {args(index)}
    val indexik = index 
    val name = s"default_tuple($fields)"
      if (arity==1) { vpr.DomainFuncApp(
      funcname = "struct_settup",
      args = Seq(vpr.LocalVarDecl(s"$name", domainType)().localVar,vpr.LocalVarDecl(s"$indexik", vpr.Int)().localVar,vpr.LocalVarDecl(s"$value", vpr.Int)().localVar),
      typVarMap = Map.empty
    )(vpr.NoPosition,vpr.NoInfo,domainType, s"StructOps",vpr.NoTrafos)}
 
    else vpr.DomainFuncApp(
      funcname = "struct_settup",
      args = Seq(helper(args.dropRight(1),fields)(vpr.NoPosition,vpr.NoInfo,vpr.NoTrafos),vpr.LocalVarDecl(s"$indexik", vpr.Int)().localVar,vpr.LocalVarDecl(s"$value", vpr.Int)().localVar),
      typVarMap = Map.empty
    )(vpr.NoPosition,vpr.NoInfo, domainType, s"StructOps",vpr.NoTrafos)








  }



  override def get(arg: vpr.Exp, index: Int, arity: Int)(pos: vpr.Position, info: vpr.Info, errT: vpr.ErrorTrafo): vpr.DomainFuncApp = {
    addNTuplesDomain(0);
    vpr.DomainFuncApp(func = vpr.DomainFunc(s"struct_gettup", Nil, vpr.TypeVar(s"T"))(domainName = s"StructOps"), Seq(vpr.DomainFuncApp(s"struct_loc", Seq(arg,vpr.LocalVarDecl(s"$index", vpr.Int)().localVar), typVarMap = Map.empty)(vpr.NoPosition,vpr.NoInfo, vpr.Int, "Struct",vpr.NoTrafos )), typVarMap = arg.typ.asInstanceOf[vpr.DomainType].typVarsMap)(pos, info, errT)
  
  }

def generatedDomains: List[vpr.Domain] = _generatedDomains

  private var _generatedDomains: List[vpr.Domain] = List.empty
 
  
  
  

  private def addNTuplesDomain(arity: Int): Unit = {
    val domainName = s"Struct"
   val domainName2: String = s"StructOps"
    val domainType = vpr.DomainType (domainName, Map (vpr.TypeVar(s"Struct")->vpr.TypeVar(s"Struct")))(Seq.empty)
    val struct_get =  vpr.DomainFunc(s"struct_gettup", Seq(vpr.LocalVarDecl("l",vpr.Int)()), vpr.TypeVar(s"T"))(domainName = domainName)
    val struct_lengthtup =  vpr.DomainFunc(s"struct_lengthtup", Seq(vpr.LocalVarDecl("x",vpr.TypeVar("Struct"))()), vpr.Int)(domainName = domainName)
    val default =  vpr.DomainFunc(s"default_tuple", Seq(vpr.LocalVarDecl("l",vpr.Int)()), vpr.TypeVar("Struct"))(domainName = domainName)
     val struct_rev =   vpr.DomainFunc(s"struct_settup", Seq(vpr.LocalVarDecl("s",domainType)(),vpr.LocalVarDecl("m",vpr.Int)(),vpr.LocalVarDecl("t",vpr.TypeVar(s"T"))()), domainType)(domainName = domainName)
   

   
  



    // there are not quantified variables for tuples of 0 arity. Thus, do not generate any axioms in this case:
    
  
    val domain2 = vpr.Domain(name="Struct", typVars= Nil, functions = Seq(vpr.DomainFunc(s"struct_loc", Seq( vpr.LocalVarDecl("s",domainType)(),vpr.LocalVarDecl("m",vpr.Int)()), vpr.Int)(domainName = domainName)),
    axioms=Nil)()
 
    val typeVarsi = Seq(vpr.TypeVar(s"T"))
    val typeVarMapka = (typeVarsi zip typeVarsi).toMap
    val s=vpr.LocalVarDecl("s", domainType)().localVar
    val t=vpr.LocalVarDecl("t", vpr.TypeVar(s"T"))().localVar
    val m=vpr.LocalVarDecl("m", vpr.Int)().localVar
    val n=vpr.LocalVarDecl("n", vpr.Int)().localVar
val first = {
vpr.NamedDomainAxiom(
        name = s"get_set_0_ax",
        exp = vpr.Forall(
          Seq(vpr.LocalVarDecl("s", vpr.DomainType(domain2,Map.empty))(),vpr.LocalVarDecl("m", vpr.Int)(), vpr.LocalVarDecl("t", vpr.TypeVar(s"T"))()),
          Seq(vpr.Trigger(Seq(vpr.DomainFuncApp(s"struct_loc", Seq(vpr.DomainFuncApp(s"struct_settup", Seq(s,m,t), typeVarMapka)(vpr.NoPosition,vpr.NoInfo,vpr.DomainType(domain2,Map.empty), domainName2,vpr.NoTrafos ),m), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName,vpr.NoTrafos )))()),
         vpr.EqCmp(
               vpr.DomainFuncApp(s"struct_gettup", Seq(vpr.DomainFuncApp(s"struct_loc", Seq(vpr.DomainFuncApp(s"struct_settup", Seq(s,m,t), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.DomainType(domain2,Map.empty), domainName2,vpr.NoTrafos ),m), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName,vpr.NoTrafos )),typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar(s"T"), domainName2,vpr.NoTrafos ),
                vpr.LocalVarDecl("t", vpr.TypeVar(s"T"))().localVar)()
        )()
      )(domainName = domainName)
}
val second = {
vpr.NamedDomainAxiom(
        name = s"get_set_1_ax",
        exp = vpr.Forall(
          Seq(vpr.LocalVarDecl("s", vpr.DomainType(domain2,Map.empty))(),vpr.LocalVarDecl("m", vpr.Int)(),vpr.LocalVarDecl("n", vpr.Int)(), vpr.LocalVarDecl("t", vpr.TypeVar(s"T"))()),
          Seq(vpr.Trigger(Seq(vpr.DomainFuncApp(s"struct_loc", Seq(vpr.DomainFuncApp(s"struct_settup", Seq(s,n,t), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.DomainType(domain2,Map.empty), domainName2,vpr.NoTrafos ),m), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName,vpr.NoTrafos )))()),
         vpr.Implies(vpr.NeCmp(m,n)(),vpr.EqCmp(
          
          vpr.DomainFuncApp(s"struct_loc", Seq(s,m), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName,vpr.NoTrafos ) ,
                vpr.DomainFuncApp(s"struct_loc", Seq(vpr.DomainFuncApp(s"struct_settup", Seq(s,n,t), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.DomainType(domain2,Map.empty), domainName2,vpr.NoTrafos ),m), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName,vpr.NoTrafos )
                         )()
        )())()
      )(domainName = domainName)
}
val third = {
vpr.NamedDomainAxiom(name= "axiom3", exp=vpr.Forall(Seq(vpr.LocalVarDecl("m", vpr.Int)()),Seq(vpr.Trigger(Seq(vpr.DomainFuncApp("default_tuple", Seq(vpr.LocalVarDecl("m", vpr.Int)().localVar),typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar("Struct"), domainName2,vpr.NoTrafos )))()), vpr.EqCmp(vpr.LocalVarDecl("m", vpr.Int)().localVar,vpr.DomainFuncApp("struct_lengthtup", Seq(vpr.DomainFuncApp("default_tuple", Seq(vpr.LocalVarDecl("m", vpr.Int)().localVar),typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar("Struct"), domainName2,vpr.NoTrafos ) ),typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName2,vpr.NoTrafos ))())() )(domainName = domainName)
}
    val domain3 = vpr.Domain(name="StructOps", typVars= Seq(vpr.TypeVar(s"T")), functions = Seq(struct_get, struct_rev, struct_lengthtup, default),
    axioms=Seq(first,second, third))()
    _generatedDomains ::= domain2
     _generatedDomains ::= domain3

  }
}
