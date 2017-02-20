(**************************************************************************)
(*                                                                        *)
(*   Typerex Tools                                                        *)
(*                                                                        *)
(*   Copyright 2011-2017 OCamlPro SAS                                     *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU General Public License version 3 described in the file       *)
(*   LICENSE.                                                             *)
(*                                                                        *)
(**************************************************************************)

module type Type = sig
  module type T
end

module Type = struct
  module type T = Type
end

module Fun (Arg : Type) = struct
  module type T = functor (_ : Arg.T) -> Type
end

module Apply (T : Type) (F : Fun(T).T) (Arg : T.T) = F(Arg)

module type T1 = sig
  module type T
end
module T1 = struct
  module type T = T1
end

module A1 = struct
  module type T = T1
end

module Id (T: Type) (Arg : T.T) = struct
  module type T = T.T
end

module M1 = Apply(T1)(Id(T1))(A1)

module Apply2 (T : Type) (F : Fun(T).T) (Arg : T.T) (App : Apply(T)(F)(Arg).T) =
  F(Arg)

module M2 = Apply2(T1)(Id(T1))(A1)(M1)
