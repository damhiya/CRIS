(* Following are default extraction settings for CRIS *)
Require Extraction.
From Stdlib Require Export ExtrOcamlBasic ExtrOcamlNativeString.

From CRIS.scheduler Require Export SchI SchHeader.

Extraction Blacklist List String Int.

Extract Constant excluded_middle_informative => "true".

Extract Constant SchI.choose_index =>
   "fun _ tids ->
      ITree.bind
        (ITree.trigger
          (subevent
            (coq_ReSum_inr (Obj.magic __) (fun _ _ _ x x0 _ ->
              coq_Cat_IFun x x0) (fun _ _ _ -> coq_Inr_sum1) __ __ __
              (coq_ReSum_inr (Obj.magic __) (fun _ _ _ x x0 _ ->
                coq_Cat_IFun x x0) (fun _ _ _ -> coq_Inr_sum1) __ __ __
                (coq_ReSum_inr (Obj.magic __) (fun _ _ _ x x0 _ ->
                  coq_Cat_IFun x x0) (fun _ _ _ -> coq_Inr_sum1) __ __ __
                  (fun _ x -> x)))) 
            (IO (""choose_index"", (Obj.magic tids))))) 
      (fun x_ -> lazy (Coq_go (RetF x_)))".

Extract Constant Sch.choose_optbool =>
   "fun h -> ITree.trigger (subevent h (IO (""choose_optbool"", Obj.magic ())))".
