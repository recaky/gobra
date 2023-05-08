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
class SharedStructComponentImpl2 extends SharedStructComponentImpl {
 
  override def finalize(addMemberFn: vpr.Member => Unit): Unit = {genDomains2 foreach addMemberFn }
  
  private var genDomains: List[vpr.Domain] = List.empty
  private var genDomains2: List[vpr.Domain] = List.empty
  private var genArities: Set[Int] = Set.empty
  private var domains: Map[Int, vpr.Domain] = Map.empty
  private var gets: Map[(Int, Int), vpr.DomainFunc] = Map.empty
  

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
   
    val domainName2: String = s"ShStructOps"
    val domainName : String = s"ShStruct"
    val T = vpr.TypeVar("T")
    val ShStruct = vpr.TypeVar(s"ShStruct")
    val typeVars = Seq(T)
    val typeVarMap = (typeVars zip typeVars).toMap
    val domainType = vpr.DomainType(domainName = domainName2, partialTypVarsMap = typeVarMap)(typeVars)
    val xdecl = vpr.LocalVarDecl("x",ShStruct)()
    val x = xdecl.localVar
    val ydecl = vpr.LocalVarDecl("y",ShStruct)()
    val y = ydecl.localVar
    val ldecl = vpr.LocalVarDecl("l",vpr.Int)()
    val l= ldecl.localVar
    val vdecl = vpr.LocalVarDecl("v",T)()

   
  
    

   
    val eqApp = ctx.equality.eq(x, y)()
    val eqAppTrigger = vpr.Trigger(Seq(eqApp))()
    val struct_get =  vpr.DomainFunc(s"struct_get", Seq(ldecl), T)(domainName = domainName2)
    val struct_length =   vpr.DomainFunc(s"struct_length", Seq(xdecl), vpr.Int)(domainName = domainName2)
    val struct_rev =   vpr.DomainFunc(s"struct_rev", Seq(vdecl), ShStruct)(domainName = domainName2)
   

    val injective = {

       vpr.AnonymousDomainAxiom(
        vpr.Forall(
           Seq(xdecl,ldecl),
           Seq(vpr.Trigger(Seq(vpr.DomainFuncApp(s"struct_get", Seq(vpr.DomainFuncApp(s"shstruct_loc", Seq(x,l), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int,domainName2,vpr.NoTrafos )), typeVarMap)(vpr.NoPosition,vpr.NoInfo, T, domainName2,vpr.NoTrafos )))()), vpr.And(vpr.GeCmp(l,vpr.IntLit(0)())(),
            vpr.And(vpr.LtCmp(l,vpr.DomainFuncApp(s"struct_length", Seq(x), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName2,vpr.NoTrafos ))() ,
            vpr.EqCmp(
            
         vpr.DomainFuncApp(s"struct_rev" , Seq(vpr.DomainFuncApp(s"struct_get", Seq(vpr.DomainFuncApp(s"shstruct_loc", Seq(x,l), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName2,vpr.NoTrafos )), typeVarMap)(vpr.NoPosition,vpr.NoInfo, T, domainName2,vpr.NoTrafos )),typeVarMap)(vpr.NoPosition,vpr.NoInfo, ShStruct, domainName2,vpr.NoTrafos)
          
            
            ,x)()
            
            
            )())())()
        )(domainName = domainName)

    }

    val equalityAxiom2 = {
      vpr.AnonymousDomainAxiom(
        vpr.Forall(
          Seq(xdecl, ydecl),
          Seq(eqAppTrigger),
         vpr.And(vpr.EqCmp(vpr.DomainFuncApp(s"struct_length", Seq(x), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName2,vpr.NoTrafos ),
           vpr.DomainFuncApp(s"struct_length", Seq(y), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName2,vpr.NoTrafos ))() ,vpr.EqCmp(
            eqApp,
           vpr.Forall(Seq(ldecl),Nil,
             vpr.And(vpr.LtCmp(l,vpr.DomainFuncApp(s"struct_length", Seq(x), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName2,vpr.NoTrafos ))() ,vpr.And(vpr.GeCmp(l,vpr.IntLit(0)())()
                ,vpr.EqCmp(
                vpr.DomainFuncApp(s"struct_get", Seq(vpr.DomainFuncApp(s"shstruct_loc", Seq(x,l), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName,vpr.NoTrafos )), typeVarMap)(vpr.NoPosition,vpr.NoInfo, T, domainName2,vpr.NoTrafos ),
                vpr.DomainFuncApp(s"struct_get", Seq(vpr.DomainFuncApp(s"shstruct_loc", Seq(x,l), typeVarMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName,vpr.NoTrafos )), typeVarMap)(vpr.NoPosition,vpr.NoInfo, T, domainName2,vpr.NoTrafos )              )())())())()

          )())()
        )()
      )(domainName = domainName2)
    }
    val domain2 = vpr.Domain(
      name = domainName2,
      typVars = Seq(T),
      functions =  Seq(struct_get,struct_length, struct_rev),
      axioms = Seq(equalityAxiom2,injective)
    )()
    val domain = vpr.Domain(name=domainName, typVars= Nil, functions = Seq(vpr.DomainFunc(s"shstruct_loc", Seq( vpr.LocalVarDecl("s",ShStruct)(),vpr.LocalVarDecl("m",vpr.Int)()), vpr.Int)(domainName = domainName)),
    axioms=Nil
    
    )()

    genDomains ::= domain
    genDomains2 ::= domain2

    domains += (0 -> domain)
    domains += (1 -> domain2)
   
    genArities += 0
  }

  /** Returns type of shared-struct domain. */
  override def typ(t: ComponentParameter)(ctx: Context): vpr.Type = {
    val arity = 1
      
    if (!(genArities contains arity)) genDomain(arity)(ctx)

    val typeVarMap = (domains(arity).typVars zip (t map (_._1))).toMap

    vpr.DomainType(
      domain = domains(arity),
      typVarsMap = Map(vpr.TypeVar("T")->vpr.Ref)
    )
  }
 

  /** Getter of shared-struct domain. */
  override def get(base: vpr.Exp, idx: Int, t: ComponentParameter)(src: in.Node)(ctx: Context): vpr.Exp = {
    val arity = 0
    val domainName: String = s"ShStructOps"
    
   
  
    
    if (!(genArities contains arity)) genDomain(arity)(ctx)
    val (pos, info, errT) = src.vprMeta
    vpr.DomainFuncApp(func = vpr.DomainFunc(s"struct_get", Nil, vpr.Ref)(domainName = s"ShStructOps"), Seq(vpr.DomainFuncApp(s"shstruct_loc", Seq(base,vpr.LocalVarDecl(s"$idx", vpr.Int)().localVar), base.typ.asInstanceOf[vpr.DomainType].typVarsMap)(vpr.NoPosition,vpr.NoInfo, vpr.Int, domainName,vpr.NoTrafos )), base.typ.asInstanceOf[vpr.DomainType].typVarsMap)(pos, info, errT)
  }


}
