theory Bakery
  imports 
    Main

begin

record order =
  amount :: nat

find_theorems Record

type_synonym orders = "order set"

fun place_order :: "orders \<Rightarrow> order \<Rightarrow> orders" where
"place_order os order = insert order os"

fun server :: "orders \<Rightarrow> order \<Rightarrow> orders" where
"server os order = place_order os order"

fun place_order_client_server :: "orders \<Rightarrow> order \<Rightarrow> orders" where
"place_order_client_server os order = server os order"

theorem "place_order_client_server os order = place_order os order"
  by simp

type_synonym http_data = string

(* Buggy implementation - requires nat be < 256 
fun serialize :: "order \<Rightarrow> http_data" where
"serialize ord = [char_of (amount ord)]"
*)

(* Buggy impl - can only convert one char < 256
fun deserialize :: "http_data \<Rightarrow> order" where
"deserialize d = (
  let amt = of_char (hd d) in
  \<lparr> amount = amt \<rparr>
)"
*)

fun digit_list :: "nat \<Rightarrow> nat list" where
"digit_list 0 = []" |
"digit_list n = n mod 10 # digit_list (n div 10)"

definition string_of_nat :: "nat \<Rightarrow> string" where
"string_of_nat n = map char_of (digit_list n)"

fun nat_of_string :: "string \<Rightarrow> nat" where
"nat_of_string [] = 0" |
"nat_of_string (d # ds) = (of_char d) + 10 * (nat_of_string ds)"

lemma ser_deser[simp]: "nat_of_string (string_of_nat n) = n"
  apply(induction n rule: digit_list.induct)
   apply(auto simp: string_of_nat_def)
  done

definition deserialize :: "http_data \<Rightarrow> order" where
"deserialize d = \<lparr> amount = (nat_of_string d) \<rparr>"

definition serialize :: "order \<Rightarrow> http_data" where
"serialize ord = string_of_nat (amount ord)"

definition http_server :: "http_data \<Rightarrow> orders \<Rightarrow> orders" where
"http_server d os = place_order os (deserialize d)"
  
definition place_order_http :: "orders \<Rightarrow> order \<Rightarrow> orders" where
"place_order_http os order = http_server (serialize order) os"

theorem "deserialize (serialize order) = order"
  apply(cases order)
  apply(simp add: serialize_def deserialize_def)
  done
 
theorem "place_order_http os order = place_order os order"
  apply(cases order)
  apply(simp add: serialize_def deserialize_def http_server_def place_order_http_def)
  done

end