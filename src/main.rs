use rust_yul::{rules, LLL};
use egg::*;

fn main() {
    let expr: RecExpr<LLL> = "(let five 5
     (let add-five (lll x (+ (var x) (var five)))
     (let five 6
     (app (var add-five) 1))))"
        .parse()
        .unwrap();

    let runner = Runner::default().with_expr(&expr).run(&rules());
    let mut extractor = Extractor::new(&runner.egraph, AstSize);
    let (_, best_expr) = extractor.find_best(runner.roots[0]);
    println!("{}", best_expr);
}
