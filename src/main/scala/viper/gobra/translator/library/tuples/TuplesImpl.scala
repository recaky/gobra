// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.
package viper.gobra.translator.library.tuples
import scala.language.postfixOps

import viper.gobra.translator.Names
import viper.silver.{ast => vpr}

import scala.collection.mutable

class TuplesImpl extends Tuples {

  /**
    * Finalizes translation. `addMemberFn` is called with any member that is part of the encoding.
    */
  override def finalize(addMemberFn: vpr.Member => Unit): Unit = {
    generatedDomains.take(2) foreach addMemberFn
  }

  override def typ(args: Vector[vpr.Type]): vpr.DomainType = {
    val arity = 0

    vpr.DomainType(
      domain = vpr.Domain(name="Struct", typVars= Nil, functions = Seq(vpr.DomainFunc(s"struct_loc", Seq( vpr.LocalVarDecl("s",vpr.TypeVar(s"Struct"))(),vpr.LocalVarDecl("m",vpr.Int)()), vpr.Int)(domainName = "Struct")),
    axioms=Nil
    
    )(),
      typVarsMap = typeVarMap(args)
    )
  }

  override def create(args: Vector[vpr.Exp])(pos: vpr.Position, info: vpr.Info, errT: vpr.ErrorTrafo): vpr.DomainFuncApp = {
   
    println(args)
    val arity = args.size
    val index = arity - 1
    val value = if (!args.isEmpty) {args(index)}
    val indexik = index -1
    val name = if (!args.isEmpty) {args(0)}
    if (arity==1) { vpr.DomainFuncApp(
      funcname = "struct_settup",
      args = Seq(vpr.LocalVarDecl(s"$name", vpr.TypeVar("Struct"))().localVar,vpr.LocalVarDecl(s"$indexik", vpr.Int)().localVar,vpr.LocalVarDecl(s"$value", vpr.Int)().localVar),
      typVarMap = typeVarMap(args map (_.typ))
    )(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar("Struct"), s"StructOps",vpr.NoTrafos)}


    else if (arity==2) { vpr.DomainFuncApp(
      funcname = "struct_settup",
      args = Seq(vpr.LocalVarDecl(s"$name", vpr.TypeVar("Struct"))().localVar,vpr.LocalVarDecl(s"$indexik", vpr.Int)().localVar,vpr.LocalVarDecl(s"$value", vpr.Int)().localVar),
      typVarMap = typeVarMap(args map (_.typ))
    )(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar("Struct"), s"StructOps",vpr.NoTrafos)}
 
    else vpr.DomainFuncApp(
      funcname = "struct_settup",
      args = Seq(create(args.dropRight(1))(vpr.NoPosition,vpr.NoInfo,vpr.NoTrafos),vpr.LocalVarDecl(s"$indexik", vpr.Int)().localVar,vpr.LocalVarDecl(s"$value", vpr.Int)().localVar),
      typVarMap = typeVarMap(args map (_.typ))
    )(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar("Struct"), s"StructOps",vpr.NoTrafos)
  }

  override def get(arg: vpr.Exp, index: Int, arity: Int)(pos: vpr.Position, info: vpr.Info, errT: vpr.ErrorTrafo): vpr.DomainFuncApp = {
    vpr.DomainFuncApp(func = vpr.DomainFunc(s"struct_gettup", Nil, vpr.TypeVar(s"T"))(domainName = s"StructOps"), Seq(vpr.DomainFuncApp(s"struct_loc", Seq(arg,vpr.LocalVarDecl(s"$index", vpr.Int)().localVar), typVarMap = arg.typ.asInstanceOf[vpr.DomainType].typVarsMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, s"da",vpr.NoTrafos )), typVarMap = arg.typ.asInstanceOf[vpr.DomainType].typVarsMap)(pos, info, errT)
  }

  def tuple(arity: Int,args:Vector[vpr.Exp]): vpr.DomainFunc =
    constructors.getOrElse(arity, {addNTuplesDomain(arity); constructors(arity)})
  def getter(index: Int, arity: Int): vpr.DomainFunc =
    getters.getOrElse((index, arity), {addNTuplesDomain(arity); getters((index, arity))})

  def domain(arity: Int): vpr.Domain =
    domains.getOrElse(arity, {addNTuplesDomain(arity); domains(arity)})

  def typeVarMap(ts: Vector[vpr.Type]): Map[vpr.TypeVar, vpr.Type] =
    domain(ts.length).typVars.zip(ts).toMap

  def generatedDomains: List[vpr.Domain] = _generatedDomains

  private var _generatedDomains: List[vpr.Domain] = List.empty
  private val domains: mutable.Map[Int, vpr.Domain] = mutable.Map.empty
  private val constructors: mutable.Map[Int, vpr.DomainFunc] = mutable.Map.empty
  private val getters: mutable.Map[(Int,Int), vpr.DomainFunc] = mutable.Map.empty

  private def addNTuplesDomain(arity: Int): Unit = {
    val domainName = s"Struct"
    
    val typeVars = (0 until arity) map (i => vpr.TypeVar(s"T"))
    val decls = 0.until(arity) map (ix => vpr.LocalVarDecl(s"t$ix", typeVars(ix))())
    val vars = decls map (_.localVar)
    val typVarMap = typeVars.zip(typeVars).toMap

    val domainTyp = vpr.DomainType(domainName, typVarMap)(typeVars)
    val domainDecl = vpr.LocalVarDecl("p", domainTyp)()
    val domainVar = domainDecl.localVar
    val struct_get =  vpr.DomainFunc(s"struct_gettup", Seq(vpr.LocalVarDecl("l",vpr.Int)()), vpr.TypeVar(s"T"))(domainName = domainName)
    
    val struct_rev =   vpr.DomainFunc(s"struct_settup", Seq(vpr.LocalVarDecl("s",vpr.TypeVar(s"Struct"))(),vpr.LocalVarDecl("m",vpr.Int)(),vpr.LocalVarDecl("t",vpr.TypeVar(s"T"))()), vpr.TypeVar(s"Struct"))(domainName = domainName)
   

    val tupleFunc = vpr.DomainFunc(s"tuple$arity",decls, domainTyp)(domainName = domainName)
    val getFuncs = 0.until(arity) map (ix =>
      vpr.DomainFunc(s"get${ix}of$arity", Seq(domainDecl), typeVars(ix))(domainName = domainName)
      )



    // there are not quantified variables for tuples of 0 arity. Thus, do not generate any axioms in this case:
    
  
     val domain2 = vpr.Domain(name="Struct", typVars= Nil, functions = Seq(vpr.DomainFunc(s"struct_loc", Seq( vpr.LocalVarDecl("s",vpr.TypeVar(s"Struct"))(),vpr.LocalVarDecl("m",vpr.Int)()), vpr.Int)(domainName = domainName)),
    axioms=Nil
    
    )()
 
    val typeVarsi = Seq(vpr.TypeVar(s"T"))
    val typeVarMapka = (typeVarsi zip typeVarsi).toMap
    val s=vpr.LocalVarDecl("s", vpr.TypeVar(s"Struct"))().localVar
    val t=vpr.LocalVarDecl("t", vpr.TypeVar(s"T"))().localVar
    val m=vpr.LocalVarDecl("m", vpr.Int)().localVar
    val n=vpr.LocalVarDecl("n", vpr.Int)().localVar
val first = {
vpr.NamedDomainAxiom(
        name = s"get_set_0_ax",
        exp = vpr.Forall(
          Seq(vpr.LocalVarDecl("s", vpr.TypeVar(s"Struct"))(),vpr.LocalVarDecl("m", vpr.Int)(), vpr.LocalVarDecl("t", vpr.TypeVar(s"T"))()),
          Seq(vpr.Trigger(Seq(vpr.DomainFuncApp(s"struct_loc", Seq(vpr.DomainFuncApp(s"struct_settup", Seq(s,m,t), typeVarMapka)(vpr.NoPosition,vpr.NoInfo,vpr.TypeVar(s"Struct"), s"da",vpr.NoTrafos ),m), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar(s"Int"), s"da",vpr.NoTrafos )))()),
         vpr.EqCmp(
               vpr.DomainFuncApp(s"struct_gettup", Seq( vpr.DomainFuncApp(s"struct_loc", Seq(vpr.DomainFuncApp(s"struct_settup", Seq(s,m,t), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar(s"Struct"), s"da",vpr.NoTrafos ),m), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.Int, s"da",vpr.NoTrafos )),typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar(s"T"), s"da",vpr.NoTrafos ),
                vpr.LocalVarDecl("t", vpr.TypeVar(s"T"))().localVar           )()
        )()
      )(domainName = domainName)
}
val second = {
vpr.NamedDomainAxiom(
        name = s"get_set_1_ax",
        exp = vpr.Forall(
          Seq(vpr.LocalVarDecl("s", vpr.TypeVar(s"Struct"))(),vpr.LocalVarDecl("m", vpr.Int)(),vpr.LocalVarDecl("n", vpr.Int)(), vpr.LocalVarDecl("t", vpr.TypeVar(s"T"))()),
          Seq(vpr.Trigger(Seq(vpr.DomainFuncApp(s"struct_loc", Seq(vpr.DomainFuncApp(s"struct_settup", Seq(s,n,t), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar(s"Struct"), s"da",vpr.NoTrafos ),m), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.Int, s"da",vpr.NoTrafos )))()),
         vpr.Implies(vpr.NeCmp(m,n)(),vpr.EqCmp(
          
          vpr.DomainFuncApp(s"struct_loc", Seq(s,m), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.Int, s"da",vpr.NoTrafos ) ,
                vpr.DomainFuncApp(s"struct_loc", Seq(vpr.DomainFuncApp(s"struct_settup", Seq(s,n,t), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar(s"Struct"), s"da",vpr.NoTrafos ),m), typeVarMapka)(vpr.NoPosition,vpr.NoInfo, vpr.Int, s"da",vpr.NoTrafos )
                         )()
        )())()
      )(domainName = domainName)
}
    val domain3 = vpr.Domain(name="StructOps", typVars= (0 until 1) map (i=> vpr.TypeVar("T")), functions = Seq(struct_get, struct_rev),
    axioms=Seq(first,second)
    
    )()





    domains.update(arity, domain2)
 
    constructors.update(arity, tupleFunc)
    (0 until arity) foreach (ix => getters.update((ix, arity), getFuncs(ix)))


    _generatedDomains ::= domain2
     _generatedDomains ::= domain3

  }
}
