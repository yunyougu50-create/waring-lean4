import WaringGkLower

namespace Waring

#check @IsSumOfPowersAtMost
#check @waringLowerNum
#check @gk_lower_bound

#print axioms gk_lower_bound
#print axioms div_three_pow_two_pow_le

-- sanity: 对 k = 3 给出 23
example : waringLowerNum 3 = 23 := by norm_num [waringLowerNum]

end Waring
