package samurai.ai

import munit.FunSuite
import samurai.util.Json

class AiProtocolSuite extends FunSuite {

  test("AI ProofSession supports stateful proof search, branching, backtracking, suggestions, and kernel verification") {
    val session = new ProofSession()

    // 1. Load Prelude + Nat
    val loadRes = session.handleRequest(
      Json.obj(
        "id" -> Json.Num(1),
        "method" -> Json.Str("loadFile"),
        "params" -> Json.obj("path" -> Json.Str("stdlib/Nat.samurai"))
      )
    )
    assertEquals(loadRes.field("ok"), Some(Json.Bool(true)))

    // 2. Start an interactive proof: (P: Prop) => (Q: Prop) => Q => (P \/ Q)
    val startRes = session.handleRequest(
      Json.obj(
        "id" -> Json.Num(2),
        "method" -> Json.Str("startProof"),
        "params" -> Json.obj(
          "name" -> Json.Str("aiDisjunctionDemo"),
          "statement" -> Json.Str("forall (first: Prop, second: Prop) => second => (first \\/ second)")
        )
      )
    )
    assertEquals(startRes.field("ok"), Some(Json.Bool(true)))
    val state1 = startRes.field("result").flatMap(_.field("stateId")).flatMap(_.asInt).get

    // 3. Introduce binders
    val introRes = session.handleRequest(
      Json.obj(
        "id" -> Json.Num(3),
        "method" -> Json.Str("step"),
        "params" -> Json.obj("stateId" -> Json.Num(state1), "tactic" -> Json.Str("intros(first, second, proofSecond)"))
      )
    )
    assertEquals(introRes.field("ok"), Some(Json.Bool(true)))
    val branchPointState = introRes.field("result").flatMap(_.field("stateId")).flatMap(_.asInt).get

    // 4. Ask for AI tactic suggestions
    val suggestRes = session.handleRequest(
      Json.obj(
        "id" -> Json.Num(4),
        "method" -> Json.Str("suggest"),
        "params" -> Json.obj("stateId" -> Json.Num(branchPointState))
      )
    )
    val suggestedTactics = suggestRes
      .field("result")
      .flatMap(_.field("suggestions"))
      .flatMap(_.asArr)
      .get
      .flatMap(_.field("tactic").flatMap(_.asString))
    assert(suggestedTactics.contains("left"))
    assert(suggestedTactics.contains("right"))

    // 5. Explore WRONG branch (`left`), verify `assumption` fails
    val wrongBranch = session.handleRequest(
      Json.obj(
        "id" -> Json.Num(5),
        "method" -> Json.Str("step"),
        "params" -> Json.obj("stateId" -> Json.Num(branchPointState), "tactic" -> Json.Str("left"))
      )
    )
    val wrongStateId = wrongBranch.field("result").flatMap(_.field("stateId")).flatMap(_.asInt).get
    val deadEnd = session.handleRequest(
      Json.obj(
        "id" -> Json.Num(6),
        "method" -> Json.Str("step"),
        "params" -> Json.obj("stateId" -> Json.Num(wrongStateId), "tactic" -> Json.Str("assumption"))
      )
    )
    assertEquals(deadEnd.field("ok"), Some(Json.Bool(false)), "Wrong branch should fail assumption")

    // 6. BACKTRACK instantly to `branchPointState`, take `right`, then `exact(proofSecond)`!
    val rightBranch = session.handleRequest(
      Json.obj(
        "id" -> Json.Num(7),
        "method" -> Json.Str("step"),
        "params" -> Json.obj("stateId" -> Json.Num(branchPointState), "tactic" -> Json.Str("right"))
      )
    )
    val rightStateId = rightBranch.field("result").flatMap(_.field("stateId")).flatMap(_.asInt).get

    val solvedRes = session.handleRequest(
      Json.obj(
        "id" -> Json.Num(8),
        "method" -> Json.Str("step"),
        "params" -> Json.obj("stateId" -> Json.Num(rightStateId), "tactic" -> Json.Str("exact(proofSecond)"))
      )
    )
    assertEquals(solvedRes.field("ok"), Some(Json.Bool(true)))
    assertEquals(solvedRes.field("result").flatMap(_.field("isSolved")), Some(Json.Bool(true)))
    assertEquals(solvedRes.field("result").flatMap(_.field("kernelVerified")), Some(Json.Bool(true)))
    assertEquals(solvedRes.field("result").flatMap(_.field("isAxiomFree")), Some(Json.Bool(true)))

    // 7. Test lemma search
    val searchRes = session.handleRequest(
      Json.obj(
        "id" -> Json.Num(9),
        "method" -> Json.Str("searchLemmas"),
        "params" -> Json.obj("query" -> Json.Str("addComm"))
      )
    )
    val matchNames = searchRes
      .field("result")
      .flatMap(_.field("matches"))
      .flatMap(_.asArr)
      .get
      .flatMap(_.field("name").flatMap(_.asString))
    assert(matchNames.contains("addComm"))

    // 8. Reconstruct clean proof script trace from the winning stateId!
    val finalStateId = solvedRes.field("result").flatMap(_.field("stateId")).flatMap(_.asInt).get
    val traceRes = session.handleRequest(
      Json.obj(
        "id" -> Json.Num(10),
        "method" -> Json.Str("getProofTrace"),
        "params" -> Json.obj("stateId" -> Json.Num(finalStateId))
      )
    )
    assertEquals(traceRes.field("ok"), Some(Json.Bool(true)))
    val script = traceRes.field("result").flatMap(_.field("script")).flatMap(_.asString).get
    assert(script.contains("intros(first, second, proofSecond)"))
    assert(script.contains("right"))
    assert(script.contains("exact(proofSecond)"))

    // 9. Test batchStep and autoSolve!
    val startAuto = session.handleRequest(
      Json.obj(
        "id" -> Json.Num(11),
        "method" -> Json.Str("startProof"),
        "params" -> Json.obj(
          "name" -> Json.Str("aiAutoDemo"),
          "statement" -> Json.Str("forall (a: Prop, b: Prop) => (a /\\ b) => (b /\\ a)")
        )
      )
    )
    val autoState0 = startAuto.field("result").flatMap(_.field("stateId")).flatMap(_.asInt).get
    val batchRes = session.handleRequest(
      Json.obj(
        "id" -> Json.Num(12),
        "method" -> Json.Str("batchStep"),
        "params" -> Json.obj(
          "stateId" -> Json.Num(autoState0),
          "tactics" -> Json.Arr(List(Json.Str("refl"), Json.Str("intros(a, b, both)")))
        )
      )
    )
    val outcomes = batchRes.field("result").flatMap(_.field("outcomes")).flatMap(_.asArr).get
    assertEquals(outcomes.length, 2)
    assertEquals(outcomes(0).field("ok"), Some(Json.Bool(false)))
    assertEquals(outcomes(1).field("ok"), Some(Json.Bool(true)))

    val autoDone = session.handleRequest(
      Json.obj(
        "id" -> Json.Num(13),
        "method" -> Json.Str("autoSolve"),
        "params" -> Json.obj("stateId" -> Json.Num(autoState0), "maxDepth" -> Json.Num(5))
      )
    )
    assertEquals(autoDone.field("ok"), Some(Json.Bool(true)))
    assertEquals(autoDone.field("result").flatMap(_.field("kernelVerified")), Some(Json.Bool(true)))
  }
}
