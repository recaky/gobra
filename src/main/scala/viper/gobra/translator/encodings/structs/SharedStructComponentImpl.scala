// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

package viper.gobra.translator.encodings.structs

import viper.gobra.ast.{internal => in}
import viper.silver.{ast => vpr}
import StructEncoding.ComponentParameter
import viper.gobra.translator.Names
import viper.gobra.translator.context.Context

/**
  * Right now, this is just a tuples domain with an additional injectivity axiom to enable quantified permissions.
  * Because of the injectivity axiom, the constructor has to be removed. Otherwise the axioms are inconsistent.
  * */
class SharedStructComponentImpl extends SharedStructComponent {

  override def finalize(addMemberFn: vpr.Member => Unit): Unit = genDomains foreach addMemberFn

  private var genDomains: List[vpr.Domain] = List.empty
  private var genArities: Set[Int] = Set.empty
  private var domains: Map[Int, vpr.Domain] = Map.empty
  private var gets: Map[(Int, Int), vpr.DomainFunc] = Map.empty
  private var members:Int=0

  /**
    * Generates:
    * domain SharedStruct[T, ..., TN] {
    *   function get1ofN(x: SharedStruct): T
    *   ...
    *   function getNofN(x: SharedStruct): T2
    *   function rev1ofN(v1: T): SharedStruct
    *   ...
    *   function revNofN(vN: TN): SharedStruct
    *
    * axiom {
    *   forall x: SharedStruct, y: SharedStruct :: {eq(x, y)} eq(x,y) <==> get1OfN(x) == get1ofN(y) && ... && getNofN(x) == getNofN(y)
    * }
    *
    * axiom {
    *   forall x: SharedStruct :: {get1ofN(x)} rev1ofN(get1ofN(x)) == x
    * }
    *
    * ...
    *
    * axiom {
    *   forall x: SharedStruct :: {getNofN(x)} revNofN(getNofN(x)) == x
    * }
    */
  private def genDomain(arity: Int)(ctx: Context): Unit = {
   
    val domainName: String = s"ShStructOps"
    val typeVars = (0 until 1) map (i => vpr.TypeVar(s"T"))
    val typeVarMap = (typeVars zip typeVars).toMap
    val domainType = vpr.DomainType(domainName = domainName, partialTypVarsMap = typeVarMap)(typeVars)
    val xDecl = vpr.LocalVarDecl("x", domainType)()
    val x = xDecl.localVar
    val yDecl = vpr.LocalVarDecl("y", domainType)()
    val y = yDecl.localVar
   
  
    

   
    val eqApp = ctx.equality.eq(x, y)()
    val eqAppTrigger = vpr.Trigger(Seq(eqApp))()
    val struct_get =  vpr.DomainFunc(s"struct_get", Seq(vpr.LocalVarDecl("l",vpr.Int)()), vpr.TypeVar(s"T"))(domainName = domainName)
    val struct_length =   vpr.DomainFunc(s"struct_length", Seq(vpr.LocalVarDecl("x",vpr.TypeVar(s"ShStruct"))()), vpr.Int)(domainName = domainName)
    val struct_rev =   vpr.DomainFunc(s"struct_rev", Seq(vpr.LocalVarDecl("v",vpr.TypeVar(s"T"))()), vpr.TypeVar(s"ShStruct"))(domainName = domainName)
   

    val injective = {

       vpr.AnonymousDomainAxiom(
        vpr.Forall(
           Seq(vpr.LocalVarDecl("x", vpr.TypeVar(s"ShStruct"))(),vpr.LocalVarDecl("l", vpr.Int)()),
           Seq(vpr.Trigger(Seq(vpr.DomainFuncApp(s"struct_get", Seq(vpr.DomainFuncApp(s"shstruct_loc", Seq(x,vpr.LocalVarDecl("l", vpr.Int)().localVar), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, s"ShStructOps",vpr.NoTrafos )), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar(s"T"), s"ShStructOps",vpr.NoTrafos )))()), vpr.And(vpr.GeCmp((vpr.LocalVarDecl("l", vpr.Int)()).localVar,vpr.IntLit(0)())(),
            vpr.And(vpr.LtCmp(vpr.LocalVarDecl("l", vpr.Int)().localVar,vpr.DomainFuncApp(s"struct_length", Seq(x), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, s"ShStructOps",vpr.NoTrafos ))() ,
            vpr.EqCmp(
            
         vpr.DomainFuncApp(s"struct_rev" , Seq(vpr.DomainFuncApp(s"struct_get", Seq(vpr.DomainFuncApp(s"shstruct_loc", Seq(x,vpr.LocalVarDecl("l", vpr.Int)().localVar), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, s"ShStructOps",vpr.NoTrafos )), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar(s"T"), s"ShStructOps",vpr.NoTrafos )),typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar(s"ShStruct"), s"ShStructOps",vpr.NoTrafos)
          
            
            ,x)()
            
            
            )())())()
        )(domainName = domainName)

    }

    val equalityAxiom2 = {
      vpr.AnonymousDomainAxiom(
        vpr.Forall(
          Seq(vpr.LocalVarDecl("x", vpr.TypeVar(s"ShStruct"))(), vpr.LocalVarDecl("y", vpr.TypeVar(s"ShStruct"))()),
          Seq(eqAppTrigger),
         vpr.And(vpr.EqCmp(vpr.DomainFuncApp(s"struct_length", Seq(x), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, s"ShStructOps",vpr.NoTrafos ),
           vpr.DomainFuncApp(s"struct_length", Seq(y), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, s"ShStructOps",vpr.NoTrafos ))() ,vpr.EqCmp(
            eqApp,
           vpr.Forall(Seq(vpr.LocalVarDecl("l", vpr.Int)()),Nil,
             vpr.And(vpr.LtCmp(vpr.LocalVarDecl("l", vpr.Int)().localVar,vpr.DomainFuncApp(s"struct_length", Seq(x), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, s"ShStructOps",vpr.NoTrafos ))() ,vpr.And(vpr.GeCmp((vpr.LocalVarDecl("l", vpr.Int)()).localVar,vpr.IntLit(0)())()
                ,vpr.EqCmp(
                vpr.DomainFuncApp(s"struct_get", Seq(vpr.DomainFuncApp(s"shstruct_loc", Seq(x,vpr.LocalVarDecl("l", vpr.Int)().localVar), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, s"ShStruct",vpr.NoTrafos )), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar(s"T"), s"ShStructOps",vpr.NoTrafos ),
                vpr.DomainFuncApp(s"struct_get", Seq(vpr.DomainFuncApp(s"shstruct_loc", Seq(x,vpr.LocalVarDecl("l", vpr.Int)().localVar), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, s"ShStruct",vpr.NoTrafos )), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.TypeVar(s"T"), s"ShStructOps",vpr.NoTrafos )              )())())())()

          )())()
        )()
      )(domainName = domainName)
    }
    val domain2 = vpr.Domain(
      name = domainName,
      typVars = Seq(vpr.TypeVar(s"T")),
      functions =  Seq(struct_get,struct_length, struct_rev),
      axioms = Seq(equalityAxiom2,injective)
    )()
    val domain = vpr.Domain(name="ShStruct", typVars= Nil, functions = Seq(vpr.DomainFunc(s"shstruct_loc", Seq( vpr.LocalVarDecl("s",vpr.TypeVar(s"ShStruct"))(),vpr.LocalVarDecl("m",vpr.Int)()), vpr.Int)(domainName = "ShStruct")),
    axioms=Nil
    
    )()

    genDomains ::= domain
    genDomains ::= domain2

    domains += (0 -> domain)
   
    genArities += 0
  }

  /** Returns type of shared-struct domain. */
  override def typ(t: ComponentParameter)(ctx: Context): vpr.Type = {
    val arity = 0
      
    if (!(genArities contains arity)) genDomain(arity)(ctx)

    val typeVarMap = (domains(arity).typVars zip (t map (_._1))).toMap

    vpr.DomainType(
      domain = domains(arity),
      typVarsMap = typeVarMap
    )
  }

  /** Getter of shared-struct domain. */
  override def get(base: vpr.Exp, idx: Int, t: ComponentParameter)(src: in.Node)(ctx: Context): vpr.Exp = {
    val arity = 0
    val domainName: String = s"ShStructOps"
    val typeVars = (0 until arity) map (i => vpr.TypeVar(s"T$i"))
    val typeVarMap = (typeVars zip typeVars).toMap
    val domainType = vpr.DomainType(domainName = domainName, partialTypVarsMap = typeVarMap)(typeVars)
    val xDecl = vpr.LocalVarDecl("x", domainType)()
    val x = xDecl.localVar
    
    if (!(genArities contains arity)) genDomain(arity)(ctx)
    val (pos, info, errT) = src.vprMeta
    vpr.DomainFuncApp(func = vpr.DomainFunc(s"struct_get", Nil, vpr.Ref)(domainName = s"ShStructOps"), Seq(vpr.DomainFuncApp(s"shstruct_loc", Seq(base,vpr.LocalVarDecl(s"$idx", vpr.Int)().localVar), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, s"ShStruct",vpr.NoTrafos )), base.typ.asInstanceOf[vpr.DomainType].typVarsMap)(pos, info, errT)
  }


}
