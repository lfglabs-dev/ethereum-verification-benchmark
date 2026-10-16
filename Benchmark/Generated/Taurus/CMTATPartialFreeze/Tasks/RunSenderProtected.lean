import Benchmark.Cases.Taurus.CMTATPartialFreeze.Specs

namespace Benchmark.Cases.Taurus.CMTATPartialFreeze

theorem run_senderProtected (s t : State) (op : Operation) (h : run s op = .ok t) : senderProtected s t op := by
  exact ?_

end Benchmark.Cases.Taurus.CMTATPartialFreeze
