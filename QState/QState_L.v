



Require Import Classical_Prop.




Require Import ParDensityO.



#[export] Hint Resolve WF_state_dstate WF_dstate_eq WWF_dstate_aux_to_WF_dstate_aux: DState.
(*------------WF_d_scale-------------------*)

#[export] Hint Resolve WF_d_scale WF_d_scale_aux WF_d_scale_not_0 WF_dstate_empty 
WWF_d_scale_aux: DState.
(*------------------WF_d_app------------------------------*)


#[export] Hint Resolve WF_s_plus WF_d_app WF_d_app_aux WWF_d_app_aux: DState. 









