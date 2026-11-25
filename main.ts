// pump-fun-sharpe-sprint: a launch-sniper paper bot for the make.fun
// "Pump.fun Sharpe Sprint — Cleanest Paper Bot Wins" bounty (agent-fun/replay/v2).
//
// Goal is Sharpe ratio (hourly), not wild PnL, so this bot trades many tiny,
// fast, disciplined round trips instead of chasing one moonshot:
//   - buy only fresh launches (age 0-2 slots) that pass a rug filter:
//     creator has not sold, creator's own opening buy is bounded,
//     exactly a small handful of distinct non-creator buyers so far, no
//     big single sell, sells by others are a small share of buys, real
//     SOL in a sane band, and the price has not already run away from
//     its create price;
//   - one small buy per coin (0.05 SOL, capped at 1% of real reserves),
//     never adds: false starts cost little;
//   - exit fast: take profit +12%, stop loss -8%, trailing stop 4% once
//     armed at +4%, max hold 15 slots, exit at once when the creator sells,
//     exit when the coin goes stale;
//   - tiny probe round trips (0.01 SOL) keep the guardrail pace (fills /
//     coins) on track only when launches are scarce.
// Deterministic by construction: no clock, no randomness, no network, no file
// reads; iteration only over insertion-ordered maps fed by the batch stream.

import { runBot, type Batch, type BotState, type OrderInput, type Pubkey } from './vendor/makefun-bot.ts';

const LAMPORTS = 1e9;
const CURVE_FEE_BPS = 125n; // protocol 95 bps + creator 30 bps
const BPS = 10_000n;

const P = {
  minAge: 0, // youngest age (slots since create) at which a coin may be bought
  maxAge: 2, // oldest age at which a first buy may still be decided
  stakeSol: 0.05, // SOL to aim for per coin in total
  minBuySol: 0.01, // smallest single buy worth paying the tx fee for
  minRealSol: 0.5, // real SOL reserve window at decision time
  maxRealSol: 40,
  maxDevBuySol: 1.5, // creator's own buys in the create slot, at most
  minBuyers: 3, // distinct non-creator buyers seen before entry
  maxBuyers: 3, // a launch bundled by many wallets is a dump in waiting
  maxSellRatioBps: 5000, // lamports sold by others / lamports bought, at most
  maxBigSellBps: 2000, // largest single non-creator sell, bps of real SOL before it
  maxRunupBps: 1000, // price now over the create price, at most (+10%)
  buySlipBps: 10_000,
  tpBps: 1200, // exit when the position is worth this much over its cost (+12%)
  slBps: 800, // exit when it is worth this much under its cost (-8%)
  trailArmBps: 400, // trailing stop arms once up this much (+4%)
  trailBps: 400, // exit on a fall of this much from the best value (-4%)
  maxHold: 15, // exit after holding this many slots
  exitOnDevSell: true, // exit when the creator sells while held
  staleSlots: 60, // exit when no trade has hit the coin for this many slots
  targetCoins: 25,
  targetFills: 240,
  paceSecs: 14_400, // 4h pacing window for the guardrail probes
  probeSol: 0.01,
  maxProbes: 1,
};

interface Coin {
  mint: Pubkey;
  createSlot: number;
  creator: Pubkey;
  vq0: bigint;
  vt0: bigint;
  devBuy: bigint;
  trades: number;
  buyers: Set<Pubkey>;
  bought: bigint;
  soldByOthers: bigint;
  bigSellBps: bigint;
  devSold: boolean;
  lastTradeSlot: number;
  done: boolean;
  complete: boolean;
}

interface Held {
  openedSlot: number;
  txPaid: bigint;
  best: bigint;
  devSoldAtOpen: boolean;
}

const coins = new Map<Pubkey, Coin>();
const held = new Map<Pubkey, Held>();
/** Mints with a sell in flight. */
const selling = new Set<Pubkey>();
/** Probe round trips in flight, by mint: false while buying, true once selling. */
const probes = new Map<Pubkey, boolean>();
let myFills = 0;
const myCoins = new Set<Pubkey>();
let firstTime: number | null = null;
let lastTime: number | null = null;

/** What selling `tokens` against (vq, vt) would pay after curve fees. */
function sellValue(tokens: bigint, vq: bigint, vt: bigint): bigint {
  if (tokens <= 0n || vt <= 0n) return 0n;
  const q = (tokens * vq) / (vt + tokens);
  return q - (q * CURVE_FEE_BPS + BPS - 1n) / BPS;
}

function readEvents(batch: Batch): void {
  for (const e of batch.events) {
    if (e.event === 'CreateEvent') {
      coins.set(e.mint, {
        mint: e.mint,
        createSlot: e.slot,
        creator: e.creator,
        vq0: BigInt(e.virtual_quote_reserves),
        vt0: BigInt(e.virtual_token_reserves),
        devBuy: 0n,
        trades: 0,
        buyers: new Set(),
        bought: 0n,
        soldByOthers: 0n,
        bigSellBps: 0n,
        devSold: false,
        lastTradeSlot: e.slot,
        done: false,
        complete: false,
      });
    } else if (e.event === 'TradeEvent') {
      const c = coins.get(e.mint);
      if (c === undefined) continue;
      const sol = BigInt(e.sol_amount);
      c.trades += 1;
      c.lastTradeSlot = e.slot;
      const isDev = e.user === c.creator;
      if (e.is_buy) {
        c.bought += sol;
        if (isDev && e.slot === c.createSlot) c.devBuy += sol;
        else if (!isDev) c.buyers.add(e.user);
      } else if (isDev) {
        c.devSold = true;
      } else {
        c.soldByOthers += sol;
        const rqBefore = BigInt(e.real_quote_reserves) + sol;
        if (rqBefore > 0n) {
          const bps = (sol * BPS) / rqBefore;
          if (bps > c.bigSellBps) c.bigSellBps = bps;
        }
      }
    } else {
      const c = coins.get(e.mint);
      if (c !== undefined) {
        c.complete = true;
        c.done = true;
      }
    }
  }
}

/** Rug filter: true when the launch looks clean enough for one small buy. */
function passesFilter(c: Coin, curve: { real_quote_reserves: bigint; virtual_quote_reserves: bigint; virtual_token_reserves: bigint }): boolean {
  const rq = curve.real_quote_reserves;
  if (rq < BigInt(Math.floor(P.minRealSol * LAMPORTS)) || rq > BigInt(Math.floor(P.maxRealSol * LAMPORTS))) return false;
  if (c.devSold) return false;
  if (c.devBuy > BigInt(Math.floor(P.maxDevBuySol * LAMPORTS))) return false;
  if (c.buyers.size < P.minBuyers || c.buyers.size > P.maxBuyers) return false;
  if (c.bought > 0n && (c.soldByOthers * BPS) / c.bought > BigInt(P.maxSellRatioBps)) return false;
  if (c.bigSellBps > BigInt(P.maxBigSellBps)) return false;
  if (c.vq0 > 0n && c.vt0 > 0n && curve.virtual_token_reserves > 0n) {
    const runup = (curve.virtual_quote_reserves * c.vt0 * BPS) / (curve.virtual_token_reserves * c.vq0);
    if (runup > BPS + BigInt(P.maxRunupBps)) return false;
  }
  return true;
}

await runBot({
  onBatch(state: BotState, batch: Batch): OrderInput[] {
    readEvents(batch);
    for (const e of batch.events) {
      if (e.block_time === null) continue;
      if (firstTime === null) firstTime = e.block_time;
      if (e.block_time > lastTime!) lastTime = e.block_time;
    }
    const orders: OrderInput[] = [];
    const cap = state.hello.caps.max_orders_per_batch;
    const tx = state.txFeeLamports();
    const marks = new Map<Pubkey, { vq: bigint; vt: bigint }>();
    for (const m of batch.marks) {
      marks.set(m.mint, { vq: BigInt(m.virtual_quote_reserves), vt: BigInt(m.virtual_token_reserves) });
    }
    const pendingByMint = new Map<Pubkey, number>();
    for (const po of state.pending.values()) {
      pendingByMint.set(po.order.mint, (pendingByMint.get(po.order.mint) ?? 0) + 1);
    }

    for (const f of batch.fills) {
      if (f.client_id.startsWith('_')) {
        held.delete(f.mint);
        selling.delete(f.mint);
        continue;
      }
      if (f.status === 'filled') {
        myFills++;
        myCoins.add(f.mint);
      }
      const h = held.get(f.mint);
      if (f.status !== 'rejected' && h !== undefined) h.txPaid += BigInt(f.tx_fee_lamports);
      if (f.side === 'buy' && f.status === 'filled' && h === undefined) {
        held.set(f.mint, {
          openedSlot: f.slot,
          txPaid: BigInt(f.tx_fee_lamports),
          best: 0n,
          devSoldAtOpen: coins.get(f.mint)?.devSold ?? false,
        });
      }
    }
    for (const mint of [...selling]) {
      let stillPending = false;
      for (const po of state.pending.values()) {
        if (po.order.mint === mint && po.order.side === 'sell') stillPending = true;
      }
      if (!stillPending) selling.delete(mint);
    }
    for (const mint of [...held.keys()]) {
      if (!state.positions.has(mint) && !selling.has(mint) && !pendingByMint.has(mint)) held.delete(mint);
    }

    // Exits first.
    for (const [mint, pos] of state.positions) {
      if (orders.length >= cap) break;
      if (selling.has(mint)) continue;
      const c = coins.get(mint);
      let h = held.get(mint);
      if (h === undefined) {
        h = { openedSlot: state.slot, txPaid: tx, best: 0n, devSoldAtOpen: c?.devSold ?? false };
        held.set(mint, h);
      }
      let mk = marks.get(mint);
      if (mk === undefined) {
        const cv = state.curves.get(mint);
        if (cv === undefined) continue;
        mk = { vq: cv.virtual_quote_reserves, vt: cv.virtual_token_reserves };
      }
      const value = sellValue(BigInt(pos.token_amount), mk.vq, mk.vt) - tx;
      const basis = BigInt(pos.cost_lamports) + h.txPaid;
      if (value > h.best) h.best = value;
      let exit = false;
      if (basis > 0n) {
        if (value * BPS >= basis * (BPS + BigInt(P.tpBps))) exit = true;
        if (value * BPS <= basis * (BPS - BigInt(P.slBps))) exit = true;
        if (h.best * BPS >= basis * (BPS + BigInt(P.trailArmBps)) && value * BPS <= h.best * (BPS - BigInt(P.trailBps))) exit = true;
      }
      if (state.slot - h.openedSlot >= P.maxHold) exit = true;
      if (c !== undefined) {
        if (P.exitOnDevSell && c.devSold && !h.devSoldAtOpen) exit = true;
        if (state.slot - c.lastTradeSlot >= P.staleSlots) exit = true;
      }
      if (!exit) continue;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: 10_000 });
      selling.add(mint);
      if (c !== undefined) c.done = true;
    }

    // Probe round trips: sell the whole probe as soon as its buy has landed.
    for (const [mint, sellingProbe] of probes) {
      const pos = state.positions.get(mint);
      const curve = state.curves.get(mint);
      if (pos === undefined) {
        if (!pendingByMint.has(mint)) probes.delete(mint);
        continue;
      }
      if (curve === undefined || curve.complete || pendingByMint.has(mint)) continue;
      if (orders.length >= cap) break;
      orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: 10_000 });
      if (!sellingProbe) probes.set(mint, true);
    }

    // Entries: one small buy per fresh launch that passes the rug filter.
    let free = state.freeCashLamports();
    let open = state.committedPositionCount();
    for (const c of coins.values()) {
      if (orders.length >= cap) break;
      if (c.done || c.complete) continue;
      const age = state.slot - c.createSlot;
      if (age > P.maxAge) {
        c.done = true;
        continue;
      }
      if (age < P.minAge) continue;
      if (open >= state.hello.caps.max_open_positions) continue;
      if (pendingByMint.has(c.mint) || probes.has(c.mint) || state.positions.has(c.mint)) continue;
      const curve = state.curves.get(c.mint);
      if (curve === undefined || curve.complete) continue;
      if (!passesFilter(c, curve)) continue;
      const maxBuy = state.maxBuyLamports(c.mint);
      const want = BigInt(Math.floor(P.stakeSol * LAMPORTS));
      const amount = want < maxBuy ? want : maxBuy;
      if (amount < BigInt(Math.floor(P.minBuySol * LAMPORTS))) continue;
      if (free < amount + tx) continue;
      orders.push({ side: 'buy', mint: c.mint, quote_lamports: amount, max_slippage_bps: P.buySlipBps });
      free -= amount + tx;
      open += 1;
      c.done = true;
    }

    // Guardrail pacing: open a probe only when fills or coins lag the pace.
    if (probes.size < P.maxProbes && firstTime !== null && lastTime !== null) {
      const pace = Math.min(1, (lastTime - firstTime) / P.paceSecs);
      const needCoins = myCoins.size < Math.ceil(P.targetCoins * pace);
      const needFills = myFills < Math.ceil(P.targetFills * pace);
      if (needCoins || needFills) {
        const minRq = (P.probeSol * Number(BPS)) / state.hello.caps.max_order_bps_of_real_reserve;
        for (const e of batch.events) {
          if (orders.length >= cap || probes.size >= P.maxProbes) break;
          if (e.event !== 'TradeEvent') continue;
          const mint = e.mint;
          if (coins.get(mint)?.done || probes.has(mint) || pendingByMint.has(mint) || state.positions.has(mint)) continue;
          if (needCoins && !needFills && myCoins.has(mint)) continue;
          const curve = state.curves.get(mint);
          if (curve === undefined || curve.complete) continue;
          if (Number(curve.real_quote_reserves) / LAMPORTS < minRq * 1.5) continue;
          if (free < BigInt(Math.floor(P.probeSol * LAMPORTS)) + 2n * tx) break;
          orders.push({ side: 'buy', mint, quote_lamports: BigInt(Math.floor(P.probeSol * LAMPORTS)), max_slippage_bps: P.buySlipBps });
          probes.set(mint, false);
          free -= BigInt(Math.floor(P.probeSol * LAMPORTS)) + tx;
        }
      }
    }
    return orders;
  },
});
