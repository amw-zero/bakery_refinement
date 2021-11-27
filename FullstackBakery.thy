theory FullstackBakery

imports Main

begin

text "Abstract specification"

record order =
  amount :: nat

type_synonym orders = "order set"

fun place_order :: "orders \<Rightarrow> order \<Rightarrow> orders" where
"place_order os order = insert order os"

text "Refinement"

type_synonym http_data = string

fun digit_list :: "nat \<Rightarrow> nat list" where
"digit_list 0 = []" |
"digit_list n = n mod 10 # digit_list (n div 10)"

definition string_of_nat :: "nat \<Rightarrow> string" where
"string_of_nat n = map char_of (digit_list n)"

fun nat_of_string :: "string \<Rightarrow> nat" where
"nat_of_string [] = 0" |
"nat_of_string (d # ds) = (of_char d) + 10 * (nat_of_string ds)"

definition deserialize :: "http_data \<Rightarrow> order" where
"deserialize d = \<lparr> amount = (nat_of_string d) \<rparr>"

definition serialize :: "order \<Rightarrow> http_data" where
"serialize ord = string_of_nat (amount ord)"

definition http_server :: "http_data \<Rightarrow> orders \<Rightarrow> orders" where
"http_server d os = place_order os (deserialize d)"
  
definition place_order_http :: "orders \<Rightarrow> order \<Rightarrow> orders" where
"place_order_http os order = http_server (serialize order) os"

record order_view = order +
  amount_view :: string

type_synonym state = orders

type_synonym view_state = "(order_view list * state)"

definition state_from :: "view_state \<Rightarrow> state" where
"state_from vs = snd vs"

definition order_from :: "order_view \<Rightarrow> order" where
"order_from ov = \<lparr> amount = amount ov \<rparr>"

fun place_order_view :: "view_state \<Rightarrow> order_view \<Rightarrow> view_state" where
"place_order_view vs ov = 
  (let next_state = place_order_http (state_from vs) (order_from ov) in
  ((fst vs), next_state))"

definition project :: "view_state \<Rightarrow> state" where
"project vs = snd vs"

text "Refinement Correctness"

lemma ser_deser[simp]: "nat_of_string (string_of_nat n) = n"
  apply(induction n rule: digit_list.induct)
   apply(auto simp: string_of_nat_def)
  done

theorem http_equiv: "place_order_http os order = place_order os order"
  apply(cases order)
  apply(simp add: serialize_def deserialize_def http_server_def place_order_http_def)
  done

theorem
  assumes "order = ord"
  and "ov = \<lparr> amount = (amount ord), amount_view = ''123'' \<rparr>"
  shows "project (place_order_view (ovs, os) ov) = place_order os order"
  using assms
  apply(cases ord)
  apply(simp add: project_def http_equiv order_from_def state_from_def)
  done

end