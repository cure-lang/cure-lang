%{
  type: {:pi, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:data, :Nat, [], []}},
  term:
    {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []},
     {:case, {:ctor, :T, []}, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bd, [], []}, {:data, :Nat, [], []}},
      [
        {:T, 0,
         {:app,
          {:app, {:global, :plus},
           {:app, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:ctor, :S, [var: 0]}}, {:ctor, :Z, []}}},
          {:app, {:global, :dbl},
           {:case, {:ctor, :Z, []},
            {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:data, :Nat, [], []}},
            [
              {:Z, 0,
               {:case,
                {:case,
                 {:case, {:var, 1}, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bd, [], []}, {:data, :Bd, [], []}},
                  [
                    {:T, 0,
                     {:case,
                      {:case, {:var, 1},
                       {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bd, [], []}, {:data, :Bd, [], []}},
                       [{:T, 0, {:var, 1}}, {:F, 0, {:ctor, :T, []}}]},
                      {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bd, [], []}, {:data, :Bd, [], []}},
                      [{:T, 0, {:var, 1}}, {:F, 0, {:var, 1}}]}},
                    {:F, 0, {:ctor, :F, []}}
                  ]}, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bd, [], []}, {:data, :Bd, [], []}},
                 [{:T, 0, {:var, 1}}, {:F, 0, {:ctor, :T, []}}]},
                {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bd, [], []}, {:data, :Nat, [], []}},
                [
                  {:T, 0,
                   {:app,
                    {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []},
                     {:app, {:app, {:global, :plus}, {:var, 0}},
                      {:case, {:var, 5},
                       {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:data, :Nat, [], []}},
                       [
                         {:Z, 0,
                          {:case,
                           {:case, {:var, 2},
                            {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bd, [], []}, {:data, :Bd, [], []}},
                            [{:T, 0, {:ctor, :T, []}}, {:F, 0, {:ctor, :F, []}}]},
                           {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bd, [], []}, {:data, :Nat, [], []}},
                           [
                             {:T, 0, {:app, {:app, {:global, :plus}, {:ctor, :Z, []}}, {:var, 1}}},
                             {:F, 0,
                              {:app, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:var, 0}},
                               {:var, 1}}}
                           ]}},
                         {:S, 1, {:var, 0}}
                       ]}}},
                    {:app, {:app, {:global, :plus}, {:var, 0}},
                     {:app, {:global, :dbl},
                      {:case,
                       {:app,
                        {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []},
                         {:app, {:app, {:global, :plus}, {:var, 0}}, {:ctor, :Z, []}}}, {:var, 0}},
                       {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:data, :Nat, [], []}},
                       [{:Z, 0, {:app, {:app, {:global, :plus}, {:ctor, :Z, []}}, {:ctor, :Z, []}}}, {:S, 1, {:var, 0}}]}}}}},
                  {:F, 0,
                   {:case, {:var, 1},
                    {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bd, [], []}, {:data, :Nat, [], []}},
                    [
                      {:T, 0, {:ctor, :S, [{:ctor, :S, [{:ctor, :S, [{:ctor, :S, [{:ctor, :Z, []}]}]}]}]}},
                      {:F, 0, {:var, 0}}
                    ]}}
                ]}},
              {:S, 1, {:var, 0}}
            ]}}}},
        {:F, 0,
         {:case,
          {:case, {:app, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:var, 0}}, {:ctor, :Z, []}},
           {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:data, :Nat, [], []}},
           [{:Z, 0, {:app, {:global, :dbl}, {:var, 0}}}, {:S, 1, {:ctor, :S, [var: 0]}}]},
          {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:data, :Nat, [], []}},
          [
            {:Z, 0,
             {:app,
              {:app, {:global, :plus},
               {:case, {:ctor, :T, []},
                {:lam, Cure.Core.Grade.unrestricted(), {:data, :Bd, [], []}, {:data, :Nat, [], []}},
                [
                  {:T, 0, {:app, {:app, {:global, :plus}, {:var, 0}}, {:var, 0}}},
                  {:F, 0,
                   {:app, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:var, 0}},
                    {:app,
                     {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []},
                      {:app, {:app, {:global, :plus}, {:var, 0}}, {:app, {:global, :dbl}, {:ctor, :Z, []}}}},
                     {:ctor, :Z, []}}}}
                ]}},
              {:app, {:lam, Cure.Core.Grade.unrestricted(), {:data, :Nat, [], []}, {:ctor, :S, [var: 0]}},
               {:ctor, :Z, []}}}},
            {:S, 1, {:var, 0}}
          ]}}
      ]}},
  sig: :v1,
  ctx: [{:data, :Bd, [], []}, {:data, :Vec, [], [{:ctor, :Z, []}]}, {:data, :Vec, [], [var: 0]}, {:data, :Nat, [], []}]
}
