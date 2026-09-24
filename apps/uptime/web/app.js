// bend-uptime's dashboard: GET /api/monitors, each one's last 60 probes
// from /history, then /live's pushes. A file of its own because the
// server's CSP (Server.secured: default-src 'self') refuses inline script.
"use strict";
const N = 60;
const mons = new Map(); // name -> {m, hist: [probe, newest last]}

function el(tag, attrs, ...kids) {
  const e = document.createElementNS(tag === "svg" || tag === "polyline" || tag === "circle"
    ? "http://www.w3.org/2000/svg" : "http://www.w3.org/1999/xhtml", tag);
  for (const [k, v] of Object.entries(attrs || {})) e.setAttribute(k, v);
  for (const k of kids) e.append(k);
  return e;
}

function spark(hist) {
  const svg = el("svg", { class: "spark", viewBox: "0 0 160 28", preserveAspectRatio: "none" });
  if (hist.length === 0) return svg;
  const max = Math.max(1, ...hist.map((p) => p.ms));
  const x = (i) => hist.length === 1 ? 80 : (i / (hist.length - 1)) * 158 + 1;
  const y = (p) => 26 - (p.ms / max) * 24;
  svg.append(el("polyline", { points: hist.map((p, i) => x(i) + "," + y(p)).join(" ") }));
  hist.forEach((p, i) => { if (!p.up) svg.append(el("circle", { cx: x(i), cy: y(p), r: 2 })); });
  return svg;
}

function render() {
  const rows = document.getElementById("rows");
  rows.replaceChildren();
  document.getElementById("empty").hidden = mons.size !== 0;
  for (const { m, hist } of mons.values()) {
    const last = hist.length ? hist[hist.length - 1] : m.last;
    const state = last ? (last.up ? "up" : "down") : "pending";
    const tip = last && last.err ? last.err : "";
    rows.append(el("tr", {},
      el("td", {}, m.name, el("div", { class: "url" }, m.url)),
      el("td", {}, el("span", { class: "pill " + state, title: tip }, state)),
      el("td", {}, spark(hist)),
      el("td", { class: "num" }, last ? String(last.ms) : "-"),
      el("td", { class: "num" }, last ? String(last.code) : "-"),
      el("td", { class: "num" }, m.uptime_24h === null ? "-" : m.uptime_24h + "%"),
      el("td", {}, last ? last.at.replace("T", " ").slice(0, 19) : "-")));
  }
}

async function load() {
  const list = await (await fetch("/api/monitors")).json();
  mons.clear();
  await Promise.all(list.map(async (m) => {
    const h = await (await fetch("/api/monitors/" + encodeURIComponent(m.name) + "/history?limit=" + N)).json();
    mons.set(m.name, { m, hist: (h.history || []).reverse() });
  }));
  render();
}

function onProbe(p) {
  const e = mons.get(p.name);
  if (!e) { load(); return; } // a monitor added elsewhere
  e.hist.push(p);
  if (e.hist.length > N) e.hist.shift();
  e.m.state = p.up ? "up" : "down";
  render();
}

function live() {
  const pill = document.getElementById("live");
  const ws = new WebSocket((location.protocol === "https:" ? "wss://" : "ws://") + location.host + "/live");
  ws.onopen = () => { pill.textContent = "live"; pill.className = "pill up"; };
  ws.onmessage = (ev) => onProbe(JSON.parse(ev.data));
  ws.onclose = () => { pill.textContent = "live: reconnecting"; pill.className = "pill off"; setTimeout(live, 2000); };
}

load().then(live);
setInterval(load, 60000); // uptime % and deletions
