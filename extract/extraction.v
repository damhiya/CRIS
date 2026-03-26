Require Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.

From ITree Require Import ITreeDefinition.
Require Import ClassicalDescription.

Require Import SchI SchHeader Example0.

Set Extraction Output Directory "extract/coq_extracted".

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
                  (coq_ReSum_id (fun _ _ -> coq_Id_IFun) __)))) 
            (IO (""choose_index"", (Obj.magic tids))))) 
      (fun x_ -> lazy (Coq_go (RetF x_)))".

Extract Constant Sch.yield =>
   "fun h h0 ->
      Seal.sealing coq_SCH
      (iterC (fun _ ->
        ITree.bind (ITree.trigger (subevent h (IO (""choose_optbool"", (Obj.magic ()))))) (fun b ->
          match b with
          | Some y ->
            if y
            then ITree.bind
                   (ITree.trigger
                     (subevent h0 (Call (SchHdr.yield, (Any.Any.upcast ())))))
                   (fun _ -> lazy (Coq_go (RetF (Coq_inl ()))))
            else lazy (Coq_go (RetF (Coq_inl ())))
          | None -> lazy (Coq_go (RetF (Coq_inr ()))))) ())".

Separate Extraction observe ttitr.
