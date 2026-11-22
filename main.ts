import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const DEADLINE_MS = Number(process.env.MAKEFUN_DEADLINE_MS) || 50000;
const startTime = Date.now();
const deadline = startTime + DEADLINE_MS;

function checkDeadline(): boolean {
  return Date.now() >= deadline;
}

type Pos = { r: number; c: number };
const key = (p: Pos) => `${p.r},${p.c}`;
const parseKey = (k: string): Pos => {
  const [r, c] = k.split(',').map(Number);
  return { r, c };
};

const DIRS = [
  { dr: -1, dc: 0, ch: 'u' },
  { dr: 1, dc: 0, ch: 'd' },
  { dr: 0, dc: -1, ch: 'l' },
  { dr: 0, dc: 1, ch: 'r' },
];

function add(p: Pos, d: { dr: number; dc: number }): Pos {
  return { r: p.r + d.dr, c: p.c + d.dc };
}

function eq(a: Pos, b: Pos): boolean {
  return a.r === b.r && a.c === b.c;
}

function manhattan(a: Pos, b: Pos): number {
  return Math.abs(a.r - b.r) + Math.abs(a.c - b.c);
}

function parseLevel(level: string) {
  const grid = level.trimEnd().split('\n').map(line => line.split(''));
  const H = grid.length;
  const W = grid[0].length;
  const floor = new Set<string>();
  const goals = new Set<string>();
  const boxes: Pos[] = [];
  let player: Pos = { r: -1, c: -1 };

  for (let r = 0; r < H; r++) {
    for (let c = 0; c < W; c++) {
      const ch = grid[r][c];
      if (ch !== '#') {
        floor.add(key({ r, c }));
        if (ch === '.' || ch === '*' || ch === '+') goals.add(key({ r, c }));
        if (ch === '$' || ch === '*') boxes.push({ r, c });
        if (ch === '@' || ch === '+') player = { r, c };
      }
    }
  }
  return { grid, H, W, floor, goals, boxes, player };
}

function buildGraph(floor: Set<string>): Map<string, string[]> {
  const graph = new Map<string, string[]>();
  for (const k of floor) {
    const p = parseKey(k);
    const neigh: string[] = [];
    for (const d of DIRS) {
      const np = add(p, d);
      const nk = key(np);
      if (floor.has(nk)) neigh.push(nk);
    }
    graph.set(k, neigh);
  }
  return graph;
}

function tarjanArticulation(graph: Map<string, string[]>): Set<string> {
  const disc = new Map<string, number>();
  const low = new Map<string, number>();
  const parent = new Map<string, string | null>();
  const ap = new Set<string>();
  let time = 0;

  function dfs(u: string) {
    disc.set(u, ++time);
    low.set(u, time);
    let children = 0;

    for (const v of graph.get(u)!) {
      if (!disc.has(v)) {
        children++;
        parent.set(v, u);
        dfs(v);
        low.set(u, Math.min(low.get(u)!, low.get(v)!));
        if (parent.get(u) === null && children > 1) ap.add(u);
        if (parent.get(u) !== null && low.get(v)! >= disc.get(u)!) ap.add(u);
      } else if (v !== parent.get(u)) {
        low.set(u, Math.min(low.get(u)!, disc.get(v)!));
      }
    }
  }

  for (const u of graph.keys()) {
    if (!disc.has(u)) dfs(u);
  }
  return ap;
}

function floodFill(graph: Map<string, string[]>, start: string, blocked: Set<string>): Set<string> {
  const visited = new Set<string>();
  const queue = [start];
  visited.add(start);
  while (queue.length) {
    const u = queue.shift()!;
    for (const v of graph.get(u)!) {
      if (!blocked.has(v) && !visited.has(v)) {
        visited.add(v);
        queue.push(v);
      }
    }
  }
  return visited;
}

function findRooms(
  graph: Map<string, string[]>,
  playerPos: Pos,
  goals: Set<string>,
  boxes: Pos[],
  articulations: Set<string>
): Array<{ door: string; interior: Set<string>; goals: Set<string>; boxes: Pos[] }> {
  const playerKey = key(playerPos);
  const boxKeys = new Set(boxes.map(key));
  const goalToRoom = new Map<string, { door: string; interior: Set<string> }>();

  for (const g of goals) {
    let bestDoor: string | null = null;
    let bestInterior: Set<string> | null = null;
    let bestSize = Infinity;

    for (const a of articulations) {
      const blocked = new Set<string>([a]);
      const reachable = floodFill(graph, playerKey, blocked);
      if (reachable.has(g)) continue;

      const interior = floodFill(graph, g, blocked);
      
      let boxCount = 0;
      let goalCount = 0;
      for (const cell of interior) {
        if (boxKeys.has(cell)) boxCount++;
        if (goals.has(cell)) goalCount++;
      }

      if (boxCount !== goalCount) continue;

      if (interior.size < bestSize) {
        bestSize = interior.size;
        bestDoor = a;
        bestInterior = interior;
      }
    }

    if (bestDoor && bestInterior) {
      goalToRoom.set(g, { door: bestDoor, interior: bestInterior });
    }
  }

  const roomMap = new Map<string, { door: string; interior: Set<string>; goals: Set<string> }>();
  for (const [g, { door, interior }] of goalToRoom) {
    const roomKey = door + '|' + Array.from(interior).sort().join(',');
    if (!roomMap.has(roomKey)) {
      roomMap.set(roomKey, { door, interior: new Set(interior), goals: new Set() });
    }
    roomMap.get(roomKey)!.goals.add(g);
  }

  const rooms: Array<{ door: string; interior: Set<string>; goals: Set<string>; boxes: Pos[] }> = [];
  for (const { door, interior, goals: roomGoals } of roomMap.values()) {
    const roomBoxes = boxes.filter(b => interior.has(key(b)));
    rooms.push({ door, interior, goals: roomGoals, boxes: roomBoxes });
  }

  rooms.sort((a, b) => a.door.localeCompare(b.door));
  return rooms;
}

function bfsWalk(
  walkable: Set<string>,
  start: Pos,
  target: Pos,
  obstacles: Set<string>
): string | null {
  const startKey = key(start);
  const targetKey = key(target);
  if (startKey === targetKey) return '';

  const queue: Array<{ pos: Pos; path: string }> = [{ pos: start, path: '' }];
  const visited = new Set<string>([startKey]);

  while (queue.length) {
    if (checkDeadline()) return null;
    const { pos, path } = queue.shift()!;
    for (const d of DIRS) {
      const np = add(pos, d);
      const nk = key(np);
      if (nk === targetKey) return path + d.ch;
      if (walkable.has(nk) && !obstacles.has(nk) && !visited.has(nk)) {
        visited.add(nk);
        queue.push({ pos: np, path: path + d.ch });
      }
    }
  }
  return null;
}

function bfsWalkPath(
  walkable: Set<string>,
  start: Pos,
  target: Pos,
  obstacles: Set<string>
): Pos[] | null {
  const startKey = key(start);
  const targetKey = key(target);
  if (startKey === targetKey) return [start];

  const queue: Pos[] = [start];
  const prev = new Map<string, Pos>();
  prev.set(startKey, { r: -1, c: -1 });

  while (queue.length) {
    if (checkDeadline()) return null;
    const pos = queue.shift()!;
    if (eq(pos, target)) break;
    for (const d of DIRS) {
      const np = add(pos, d);
      const nk = key(np);
      if (walkable.has(nk) && !obstacles.has(nk) && !prev.has(nk)) {
        prev.set(nk, pos);
        queue.push(np);
      }
    }
  }

  if (!prev.has(targetKey)) return null;
  const path: Pos[] = [];
  let cur: Pos = target;
  while (!(cur.r === -1 && cur.c === -1)) {
    path.push(cur);
    cur = prev.get(key(cur))!;
  }
  return path.reverse();
}

const MAX_BFS_STATES = 200000;

function solveRoomOptimal(
  room: { door: string; interior: Set<string>; goals: Set<string>; boxes: Pos[] },
  playerStart: Pos,
  fullGraph: Map<string, string[]>
): { pushes: Array<{ dir: string; stand: Pos; box: Pos; newBox: Pos }>; finalPlayer: Pos } | null {
  const { interior, goals, boxes: initialBoxes, door } = room;
  
  const walkable = new Set<string>(interior);
  walkable.add(door);
  
  const boxAllowed = new Set<string>(interior);
  boxAllowed.add(door);

  const goalKeys = Array.from(goals).sort();
  const initialBoxKeys = initialBoxes.map(key).sort();

  const startState = {
    boxes: initialBoxKeys,
    player: key(playerStart),
  };

  const queue: Array<{ boxes: string[]; player: string }> = [startState];
  const visited = new Set<string>([JSON.stringify(startState)]);
  const parent = new Map<string, { prev: string; dir: string; stand: string; box: string; newBox: string }>();

  while (queue.length) {
    if (checkDeadline() || visited.size > MAX_BFS_STATES) {
      return null;
    }
    const state = queue.shift()!;
    const boxSet = new Set(state.boxes);

    if (state.boxes.length === goalKeys.length && state.boxes.every((b, i) => b === goalKeys[i])) {
      const pushes: Array<{ dir: string; stand: Pos; box: Pos; newBox: Pos }> = [];
      let curKey = JSON.stringify(state);
      while (parent.has(curKey)) {
        const p = parent.get(curKey)!;
        pushes.push({ 
          dir: p.dir, 
          stand: parseKey(p.stand), 
          box: parseKey(p.box), 
          newBox: parseKey(p.newBox) 
        });
        curKey = p.prev;
      }
      pushes.reverse();
      return { pushes, finalPlayer: parseKey(state.player) };
    }

    const obstacles = new Set(state.boxes);
    const reachable = floodFill(fullGraph, state.player, obstacles);
    const walkableReachable = new Set<string>();
    for (const k of reachable) {
      if (walkable.has(k)) walkableReachable.add(k);
    }

    for (const boxKey of state.boxes) {
      if (checkDeadline()) return null;
      const boxPos = parseKey(boxKey);
      for (const d of DIRS) {
        const behind = add(boxPos, { dr: -d.dr, dc: -d.dc });
        const beyond = add(boxPos, d);
        const behindKey = key(behind);
        const beyondKey = key(beyond);

        if (!walkableReachable.has(behindKey)) continue;
        if (!boxAllowed.has(beyondKey)) continue;
        if (boxSet.has(beyondKey)) continue;

        const newBoxes = state.boxes.map(b => (b === boxKey ? beyondKey : b)).sort();
        const newState = { boxes: newBoxes, player: boxKey };
        const newKey = JSON.stringify(newState);
        if (!visited.has(newKey)) {
          visited.add(newKey);
          parent.set(newKey, { 
            prev: JSON.stringify(state), 
            dir: d.ch, 
            stand: behindKey, 
            box: boxKey, 
            newBox: beyondKey 
          });
          queue.push(newState);
        }
      }
    }
  }
  return null;
}

function solveRoomGreedy(
  room: { door: string; interior: Set<string>; goals: Set<string>; boxes: Pos[] },
  playerStart: Pos,
  fullGraph: Map<string, string[]>,
  allBoxes: Pos[]
): { pushes: Array<{ dir: string; stand: Pos; box: Pos; newBox: Pos }>; finalPlayer: Pos } | null {
  const { interior, goals, boxes: roomBoxes, door } = room;
  
  const walkable = new Set<string>(interior);
  walkable.add(door);
  
  const boxAllowed = new Set<string>(interior);
  boxAllowed.add(door);

  const goalList = Array.from(goals).map(parseKey);
  const currentBoxes = [...roomBoxes];
  let currentPlayer = playerStart;
  const pushes: Array<{ dir: string; stand: Pos; box: Pos; newBox: Pos }> = [];

  const occupiedByOtherRooms = new Set(allBoxes.filter(b => !roomBoxes.some(rb => eq(rb, b))).map(key));

  // Simple loop detection: track recent states
  const recentStates = new Set<string>();
  const MAX_RECENT = 1000;

  function stateKey(boxes: Pos[], player: Pos): string {
    return boxes.map(key).sort().join(',') + '|' + key(player);
  }

  while (true) {
    if (checkDeadline()) return { pushes, finalPlayer: currentPlayer };

    const boxesOnGoals = currentBoxes.filter(b => goals.has(key(b)));
    if (boxesOnGoals.length === currentBoxes.length) {
      return { pushes, finalPlayer: currentPlayer };
    }

    const remainingBoxes = currentBoxes.filter(b => !goals.has(key(b)));
    let bestPush: { dir: string; stand: Pos; box: Pos; newBox: Pos; dist: number } | null = null;

    const allObstacles = new Set([...currentBoxes.map(key), ...occupiedByOtherRooms]);

    for (const box of remainingBoxes) {
      const boxPos = box;
      for (const d of DIRS) {
        const behind = add(boxPos, { dr: -d.dr, dc: -d.dc });
        const beyond = add(boxPos, d);
        const behindKey = key(behind);
        const beyondKey = key(beyond);

        if (!walkable.has(behindKey) || !boxAllowed.has(beyondKey)) continue;
        if (allObstacles.has(beyondKey)) continue;

        const reachable = floodFill(fullGraph, key(currentPlayer), allObstacles);
        if (!reachable.has(behindKey)) continue;

        const freeGoals = goalList.filter(g => !currentBoxes.some(b => eq(b, g)));
        if (freeGoals.length === 0) continue;
        const minDist = Math.min(...freeGoals.map(g => manhattan(beyond, g)));

        if (!bestPush || minDist < bestPush.dist) {
          bestPush = { dir: d.ch, stand: behind, box: boxPos, newBox: beyond, dist: minDist };
        }
      }
    }

    if (!bestPush) {
      return { pushes, finalPlayer: currentPlayer };
    }

    // Check for loops
    const nextBoxes = currentBoxes.map(b => eq(b, bestPush.box) ? bestPush.newBox : b);
    const nextStateKey = stateKey(nextBoxes, bestPush.box);
    if (recentStates.has(nextStateKey)) {
      // Loop detected, try second-best push or give up
      return { pushes, finalPlayer: currentPlayer };
    }
    recentStates.add(nextStateKey);
    if (recentStates.size > MAX_RECENT) {
      const first = recentStates.values().next().value;
      if (first !== undefined) recentStates.delete(first);
    }

    const walkPath = bfsWalkPath(walkable, currentPlayer, bestPush.stand, allObstacles);
    if (!walkPath) {
      return { pushes, finalPlayer: currentPlayer };
    }

    pushes.push(bestPush);
    currentBoxes.splice(currentBoxes.findIndex(b => eq(b, bestPush.box)), 1, bestPush.newBox);
    currentPlayer = bestPush.box;
    allObstacles.delete(key(bestPush.box));
    allObstacles.add(key(bestPush.newBox));
  }
}

function solve(level: string): string {
  const { floor, goals, boxes: initialBoxes, player } = parseLevel(level);
  const graph = buildGraph(floor);
  const articulations = tarjanArticulation(graph);
  const rooms = findRooms(graph, player, goals, initialBoxes, articulations);

  let currentPlayer = player;
  let currentBoxes = [...initialBoxes];
  let allMoves = '';

  for (const room of rooms) {
    if (checkDeadline()) break;

    const walkToDoor = bfsWalk(floor, currentPlayer, parseKey(room.door), new Set(currentBoxes.map(key)));
    if (walkToDoor) allMoves += walkToDoor;
    currentPlayer = parseKey(room.door);

    let result = solveRoomOptimal(room, currentPlayer, graph);
    
    if (!result) {
      result = solveRoomGreedy(room, currentPlayer, graph, currentBoxes);
    }
    if (!result) continue;

    for (const push of result.pushes) {
      if (checkDeadline()) break;
      const walkPath = bfsWalkPath(
        new Set([...room.interior, room.door]),
        currentPlayer,
        push.stand,
        new Set(currentBoxes.map(key))
      );
      if (walkPath) {
        for (let i = 1; i < walkPath.length; i++) {
          const prev = walkPath[i - 1];
          const cur = walkPath[i];
          if (cur.r === prev.r - 1) allMoves += 'u';
          else if (cur.r === prev.r + 1) allMoves += 'd';
          else if (cur.c === prev.c - 1) allMoves += 'l';
          else if (cur.c === prev.c + 1) allMoves += 'r';
        }
      }
      allMoves += push.dir;
      currentPlayer = push.box;
      const boxIdx = currentBoxes.findIndex(b => eq(b, push.box));
      if (boxIdx >= 0) {
        currentBoxes[boxIdx] = push.newBox;
      }
    }
    currentPlayer = result.finalPlayer;
  }

  return allMoves;
}

for (const id of readdirSync(I).sort()) {
  let moves = '';
  try {
    moves = solve(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  } catch (e) {
    moves = '';
  }
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}