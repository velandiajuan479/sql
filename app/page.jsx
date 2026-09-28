"use client";
/* ============================================================================
 * SQLab — Plataforma educativa interactiva de SQL
 * ----------------------------------------------------------------------------
 * Un único archivo React (App.jsx) listo para producción que incluye:
 *
 *  1. MOTOR SQL (sandbox en memoria, seguro): tokenizer, parser, planificador
 *     y ejecutor de un subconjunto amplio de SQL (SELECT/JOIN/GROUP BY/
 *     subconsultas/CTE/UNION/CASE/INSERT/UPDATE/DELETE/CREATE/DROP/
 *     BEGIN-COMMIT-ROLLBACK), con validación anti-inyección por lista blanca,
 *     límites de seguridad y errores didácticos en español.
 *  2. SUITE DE TESTS integrada (vista "Tests") que cubre validación,
 *     ejecución, manejo de errores y contrato de UX.
 *  3. CONTENIDO: 14 lecciones (Básico/Intermedio/Avanzado), 7 desafíos
 *     acumulativos con validación automática, referencia rápida y docs.
 *  4. UI: editor SQL con resaltado, resultados en tabla, esquema, historial,
 *     routing por hash, progreso persistente y diseño responsive minimalista.
 *
 * La sección "Docs" dentro de la app contiene el backend Node/Express de
 * referencia, tests de servidor, guía de despliegue y cómo extender el
 * contenido (el contrato executeScript() === POST /api/run).
 * ============================================================================ */

import React, {
  useState, useEffect, useRef, useMemo, useCallback, createContext, useContext
} from "react";
import { motion, AnimatePresence } from "framer-motion";

/* ===== SQLAB ENGINE START ===== */
/**
 * SqlError — error "amigable" del motor SQL educativo.
 * @property {string|null} hint Pista accionable para el estudiante.
 */
class SqlError extends Error {
  constructor(message, hint) {
    super(message);
    this.name = "SqlError";
    this.hint = hint || null;
  }
}

const MAX_SQL_LENGTH = 20000;   // longitud máxima de script aceptada
const MAX_STATEMENTS = 25;      // sentencias máximas por ejecución
const MAX_ROWS = 1000;          // filas máximas devueltas por resultado
const MAX_JOIN_PAIRS = 250000;  // tope anti-bloqueo para joins cartesianos

const SQL_KEYWORDS = new Set([
  "SELECT","FROM","WHERE","DISTINCT","AS","AND","OR","NOT","NULL","IS","IN","LIKE","BETWEEN",
  "ORDER","BY","GROUP","HAVING","LIMIT","OFFSET","ASC","DESC","JOIN","INNER","LEFT","RIGHT",
  "FULL","OUTER","CROSS","ON","INSERT","INTO","VALUES","UPDATE","SET","DELETE","CREATE","TABLE",
  "DROP","IF","EXISTS","PRIMARY","KEY","AUTOINCREMENT","DEFAULT","UNIQUE","CHECK","FOREIGN",
  "REFERENCES","WITH","UNION","ALL","INTERSECT","EXCEPT","CASE","WHEN","THEN","ELSE","END",
  "BEGIN","COMMIT","ROLLBACK","TRANSACTION","TRUE","FALSE","CAST",
  "INTEGER","INT","TEXT","REAL","NUMERIC","VARCHAR","CHAR","BOOLEAN","DATE","DATETIME",
  "DECIMAL","BIGINT","SMALLINT","FLOAT","DOUBLE","BLOB"
]);

const SQL_FUNCTIONS = new Set([
  "COUNT","SUM","AVG","MIN","MAX","UPPER","LOWER","LENGTH","ROUND","ABS","COALESCE",
  "IFNULL","NULLIF","REPLACE","SUBSTR","SUBSTRING","TRIM","CAST"
]);

/** Palabras asociadas a features de SGBD reales que NUNCA se admiten en el sandbox. */
const FORBIDDEN_WORDS = new Set([
  "ATTACH","DETACH","PRAGMA","REINDEX","VACUUM","ANALYZE","ALTER","LOAD","EXTENSION",
  "COPY","EXPORT","IMPORT","OUTFILE","DUMPFILE","SLEEP","BENCHMARK","PG_SLEEP",
  "XP_CMDSHELL","INFORMATION_SCHEMA","PG_CATALOG","SQLITE_MASTER","PG_TABLES"
]);

const AGGREGATES = new Set(["COUNT","SUM","AVG","MIN","MAX"]);

/** Convierte un texto SQL en tokens. Emite comentarios como tokens (el parser los filtra). */
function tokenize(sql) {
  const tokens = [];
  const n = sql.length;
  let i = 0;
  const push = (type, value, start, extra) => {
    tokens.push(Object.assign({ type, value, pos: start, end: i, raw: sql.slice(start, i) }, extra || {}));
  };
  while (i < n) {
    const start = i;
    const c = sql[i];
    if (c === " " || c === "\t" || c === "\n" || c === "\r" || c === "\f" || c === "\v") { i++; continue; }
    if (c === "-" && sql[i + 1] === "-") {
      while (i < n && sql[i] !== "\n") i++;
      push("comment", sql.slice(start, i), start);
      continue;
    }
    if (c === "/" && sql[i + 1] === "*") {
      const close = sql.indexOf("*/", i + 2);
      if (close === -1) throw new SqlError("Comentario /* sin cerrar.", "Cierra el comentario con */.");
      i = close + 2;
      push("comment", sql.slice(start, i), start);
      continue;
    }
    if (c === "'") {
      let j = i + 1;
      let val = "";
      for (;;) {
        if (j >= n) throw new SqlError("Texto sin cerrar: falta la comilla final (').", "Los textos van entre comillas simples, p. ej. 'Madrid'. Para incluir una comilla dentro, duplícala: ''.");
        if (sql[j] === "'") {
          if (sql[j + 1] === "'") { val += "'"; j += 2; continue; }
          break;
        }
        val += sql[j]; j++;
      }
      i = j + 1;
      push("string", val, start);
      continue;
    }
    if (c === '"' || c === "`") {
      let j = i + 1;
      let val = "";
      while (j < n && sql[j] !== c) { val += sql[j]; j++; }
      if (j >= n) throw new SqlError("Identificador entre " + c + " sin cerrar.");
      i = j + 1;
      push("ident", val, start, { quoted: true });
      continue;
    }
    const numMatch = /^\d+(?:\.\d+)?/.exec(sql.slice(i));
    if (numMatch) { i += numMatch[0].length; push("number", parseFloat(numMatch[0]), start); continue; }
    const idMatch = /^[A-Za-z_\u00C0-\u00DC][A-Za-z0-9_\u00C0-\u00DC]*/.exec(sql.slice(i));
    if (idMatch) {
      i += idMatch[0].length;
      const word = idMatch[0];
      const up = word.toUpperCase();
      if (SQL_KEYWORDS.has(up)) push("kw", up, start);
      else push("ident", word, start);
      continue;
    }
    const two = sql.slice(i, i + 2);
    if (two === ">=" || two === "<=" || two === "<>" || two === "!=" || two === "||") {
      i += 2;
      push("op", two === "!=" ? "<>" : two, start);
      continue;
    }
    if ("=<>+-*/%(),;.".indexOf(c) !== -1) { i++; push("op", c, start); continue; }
    throw new SqlError('Carácter no reconocido: "' + c + '" (posición ' + (start + 1) + ").", "Revisa el texto de la consulta.");
  }
  tokens.push({ type: "eof", value: null, pos: n, end: n, raw: "" });
  return tokens;
}

/** Parser descendente recursivo: tokens -> AST. */
class Parser {
  constructor(tokens) {
    this.t = tokens.filter((tk) => tk.type !== "comment");
    this.i = 0;
  }
  peek(off) { return this.t[Math.min(this.i + (off || 0), this.t.length - 1)]; }
  get cur() { return this.t[this.i]; }
  isKw(k, off) { const t = this.peek(off); return t.type === "kw" && t.value === k; }
  eatKw(k) { if (this.isKw(k)) { this.i++; return true; } return false; }
  expectKw(k) { if (!this.eatKw(k)) throw this.err('Se esperaba la palabra clave "' + k + '".'); }
  isOp(op, off) { const t = this.peek(off); return t.type === "op" && t.value === op; }
  eatOp(op) { if (this.isOp(op)) { this.i++; return true; } return false; }
  expectOp(op) { if (!this.eatOp(op)) throw this.err('Se esperaba "' + op + '".'); }
  err(msg) {
    const t = this.cur;
    const near = t.type === "eof" ? "el final de la consulta" : '"' + (t.raw || String(t.value)) + '"';
    return new SqlError("Error de sintaxis cerca de " + near + " (posición " + (t.pos + 1) + "). " + msg,
      "Revisa la estructura de la sentencia alrededor de esa posición.");
  }
  /** Consume un identificador (nombre de tabla, columna o alias). Acepta keywords como nombres. */
  ident() {
    const t = this.cur;
    if (t.type === "ident" || t.type === "kw") {
      this.i++;
      return { name: t.quoted ? t.value : String(t.value).toLowerCase(), pos: t.pos };
    }
    throw this.err("Se esperaba un nombre (identificador).");
  }
  exprList() {
    const list = [];
    do { list.push(this.expr()); } while (this.eatOp(","));
    return list;
  }

  /** Programa completo: sentencias separadas por ';'. */
  parseProgram() {
    const stmts = [];
    for (;;) {
      while (this.eatOp(";")) { /* separadores vacíos */ }
      if (this.cur.type === "eof") break;
      stmts.push(this.statement());
      if (this.cur.type !== "eof" && !this.isOp(";")) {
        throw this.err('Texto inesperado después de una sentencia completa. ¿Falta un ";" o sobra algo?');
      }
    }
    return stmts;
  }

  statement() {
    const t = this.cur;
    if (t.type !== "kw") {
      throw this.err("Toda sentencia debe empezar por una palabra clave (SELECT, WITH, INSERT, UPDATE, DELETE, CREATE, DROP, BEGIN, COMMIT o ROLLBACK).");
    }
    switch (t.value) {
      case "SELECT": return this.select();
      case "WITH": return this.select();
      case "INSERT": return this.insert();
      case "UPDATE": return this.update();
      case "DELETE": return this.deleteStmt();
      case "CREATE": return this.create();
      case "DROP": return this.drop();
      case "BEGIN": this.i++; this.eatKw("TRANSACTION"); return { type: "begin" };
      case "COMMIT": this.i++; this.eatKw("TRANSACTION"); return { type: "commit" };
      case "ROLLBACK": this.i++; this.eatKw("TRANSACTION"); return { type: "rollback" };
      default: throw this.err('La sentencia "' + t.value + '" no está permitida en este entorno educativo.');
    }
  }

  withClause() {
    this.expectKw("WITH");
    const ctes = [];
    do {
      const name = this.ident().name;
      this.expectKw("AS");
      this.expectOp("(");
      const query = this.select();
      this.expectOp(")");
      ctes.push({ name, query });
    } while (this.eatOp(","));
    const main = this.selectCore();
    return { type: "with", ctes, main };
  }

  select() {
    let node = this.selectBody();
    while (this.cur.type === "kw" && (this.cur.value === "UNION" || this.cur.value === "INTERSECT" || this.cur.value === "EXCEPT")) {
      const op = this.cur.value; this.i++;
      const all = op === "UNION" ? this.eatKw("ALL") : false;
      const right = this.selectBody();
      node = { type: "setop", op, all, left: node, right };
    }
    return node;
  }
  selectBody() { return this.isKw("WITH") ? this.withClause() : this.selectCore(); }

  selectCore() {
    this.expectKw("SELECT");
    const distinct = this.eatKw("DISTINCT");
    const items = [];
    do {
      if (this.isOp("*")) { this.i++; items.push({ star: true }); }
      else {
        const expr = this.expr();
        let alias = null;
        if (this.eatKw("AS")) alias = this.ident().name;
        else if (this.cur.type === "ident") alias = this.ident().name;
        items.push({ expr, alias });
      }
    } while (this.eatOp(","));

    const node = { type: "select", distinct, items };
    if (this.eatKw("FROM")) {
      node.from = this.tableRef();
      node.joins = [];
      for (;;) {
        let jt = null;
        if (this.isKw("INNER")) { this.i++; this.expectKw("JOIN"); jt = "inner"; }
        else if (this.isKw("LEFT")) { this.i++; this.eatKw("OUTER"); this.expectKw("JOIN"); jt = "left"; }
        else if (this.isKw("RIGHT")) { this.i++; this.eatKw("OUTER"); this.expectKw("JOIN"); jt = "right"; }
        else if (this.isKw("FULL")) { this.i++; this.eatKw("OUTER"); this.expectKw("JOIN"); jt = "full"; }
        else if (this.isKw("CROSS")) { this.i++; this.expectKw("JOIN"); jt = "cross"; }
        else if (this.eatKw("JOIN")) { jt = "inner"; }
        else if (this.isOp(",")) { this.i++; node.joins.push({ joinType: "cross", ref: this.tableRef(), on: null }); continue; }
        else break;
        const ref = this.tableRef();
        let on = null;
        if (this.eatKw("ON")) on = this.expr();
        node.joins.push({ joinType: jt, ref, on });
      }
    }
    if (this.eatKw("WHERE")) node.where = this.expr();
    if (this.isKw("GROUP")) { this.i++; this.expectKw("BY"); node.groupBy = this.exprList(); }
    if (this.eatKw("HAVING")) node.having = this.expr();
    if (this.isKw("ORDER")) {
      this.i++; this.expectKw("BY");
      node.orderBy = [];
      do {
        const expr = this.expr();
        let dir = "asc";
        if (this.eatKw("ASC")) dir = "asc";
        else if (this.eatKw("DESC")) dir = "desc";
        node.orderBy.push({ expr, dir });
      } while (this.eatOp(","));
    }
    if (this.eatKw("LIMIT")) {
      const t = this.cur;
      if (t.type !== "number") throw this.err("LIMIT debe ir seguido de un número.");
      this.i++; node.limit = t.value;
      if (this.eatKw("OFFSET")) {
        const t2 = this.cur;
        if (t2.type !== "number") throw this.err("OFFSET debe ir seguido de un número.");
        this.i++; node.offset = t2.value;
      } else if (this.isOp(",")) {
        this.i++;
        const t3 = this.cur;
        if (t3.type !== "number") throw this.err("Se esperaba un número tras la coma de LIMIT.");
        this.i++; node.offset = node.limit; node.limit = t3.value;
      }
    }
    return node;
  }

  tableRef() {
    if (this.isOp("(")) {
      this.i++;
      if (this.isKw("SELECT") || this.isKw("WITH")) {
        const query = this.select();
        this.expectOp(")");
        this.eatKw("AS");
        if (this.cur.type !== "ident" && this.cur.type !== "kw") {
          throw this.err("Toda subconsulta en FROM necesita un alias, p. ej. ... ) AS t.");
        }
        const alias = this.ident().name;
        return { type: "subquery", query, alias };
      }
      throw this.err("Los paréntesis en FROM solo se admiten para subconsultas con alias.");
    }
    const name = this.ident().name;
    let alias = null;
    if (this.eatKw("AS")) alias = this.ident().name;
    else if (this.cur.type === "ident") alias = this.ident().name;
    return { type: "table", name, alias: alias || name };
  }

  insert() {
    this.expectKw("INSERT"); this.expectKw("INTO");
    const table = this.ident().name;
    let columns = null;
    if (this.isOp("(")) {
      this.i++;
      columns = [];
      do { columns.push(this.ident().name); } while (this.eatOp(","));
      this.expectOp(")");
    }
    if (this.isKw("SELECT") || this.isKw("WITH")) {
      return { type: "insert", table, columns, select: this.select() };
    }
    this.expectKw("VALUES");
    const valuesList = [];
    do {
      this.expectOp("(");
      const vals = [];
      do { vals.push(this.expr()); } while (this.eatOp(","));
      this.expectOp(")");
      valuesList.push(vals);
    } while (this.eatOp(","));
    return { type: "insert", table, columns, valuesList };
  }

  update() {
    this.expectKw("UPDATE");
    const table = this.ident().name;
    let alias = null;
    if (this.eatKw("AS")) alias = this.ident().name;
    else if (this.cur.type === "ident") alias = this.ident().name;
    this.expectKw("SET");
    const assigns = [];
    do {
      const column = this.ident().name;
      this.expectOp("=");
      const expr = this.expr();
      assigns.push({ column, expr });
    } while (this.eatOp(","));
    let where = null;
    if (this.eatKw("WHERE")) where = this.expr();
    return { type: "update", table, alias: alias || table, assigns, where };
  }

  deleteStmt() {
    this.expectKw("DELETE"); this.expectKw("FROM");
    const table = this.ident().name;
    let alias = null;
    if (this.eatKw("AS")) alias = this.ident().name;
    else if (this.cur.type === "ident") alias = this.ident().name;
    let where = null;
    if (this.eatKw("WHERE")) where = this.expr();
    return { type: "delete", table, alias: alias || table, where };
  }

  create() {
    this.expectKw("CREATE"); this.expectKw("TABLE");
    let ifNotExists = false;
    if (this.isKw("IF")) { this.i++; this.expectKw("NOT"); this.expectKw("EXISTS"); ifNotExists = true; }
    const name = this.ident().name;
    if (this.eatKw("AS")) {
      const query = this.select();
      return { type: "create", name, ifNotExists, asSelect: query };
    }
    this.expectOp("(");
    const TYPE_WORDS = ["INTEGER","INT","TEXT","REAL","NUMERIC","VARCHAR","CHAR","BOOLEAN","DATE","DATETIME","DECIMAL","BIGINT","SMALLINT","FLOAT","DOUBLE","BLOB"];
    const columns = [];
    do {
      const col = this.ident().name;
      let dataType = "TEXT";
      const tt = this.cur;
      if ((tt.type === "kw" && TYPE_WORDS.indexOf(tt.value) !== -1) || tt.type === "ident") {
        dataType = String(tt.value).toUpperCase();
        this.i++;
        if (this.isOp("(")) { this.i++; while (!this.isOp(")") && this.cur.type !== "eof") this.i++; this.expectOp(")"); }
      }
      const def = { name: col, type: dataType, notNull: false, primaryKey: false, unique: false, defaultValue: null, autoincrement: false };
      for (;;) {
        if (this.isKw("PRIMARY")) { this.i++; this.expectKw("KEY"); def.primaryKey = true; def.notNull = true; if (this.eatKw("AUTOINCREMENT")) def.autoincrement = true; continue; }
        if (this.eatKw("AUTOINCREMENT")) { def.autoincrement = true; continue; }
        if (this.isKw("NOT")) { this.i++; this.expectKw("NULL"); def.notNull = true; continue; }
        if (this.eatKw("NULL")) { continue; }
        if (this.eatKw("UNIQUE")) { def.unique = true; continue; }
        if (this.eatKw("DEFAULT")) { def.defaultValue = this.primary(); continue; }
        if (this.isKw("REFERENCES")) { this.i++; this.ident(); if (this.isOp("(")) { this.i++; this.ident(); this.expectOp(")"); } continue; }
        if (this.eatKw("CHECK")) {
          this.expectOp("(");
          let depth = 1;
          while (depth > 0 && this.cur.type !== "eof") {
            if (this.isOp("(")) depth++;
            else if (this.isOp(")")) { depth--; if (depth === 0) break; }
            this.i++;
          }
          this.expectOp(")");
          continue;
        }
        break;
      }
      columns.push(def);
    } while (this.eatOp(","));
    this.expectOp(")");
    return { type: "create", name, ifNotExists, columns };
  }

  drop() {
    this.expectKw("DROP"); this.expectKw("TABLE");
    let ifExists = false;
    if (this.isKw("IF")) { this.i++; this.expectKw("EXISTS"); ifExists = true; }
    const name = this.ident().name;
    return { type: "drop", name, ifExists };
  }

  /* ---- Expresiones (precedencia: OR < AND < NOT < comparación < suma < producto < unario < primario) ---- */
  expr() { return this.orExpr(); }
  orExpr() {
    let left = this.andExpr();
    while (this.eatKw("OR")) left = { type: "bin", op: "OR", left, right: this.andExpr() };
    return left;
  }
  andExpr() {
    let left = this.notExpr();
    while (this.eatKw("AND")) left = { type: "bin", op: "AND", left, right: this.notExpr() };
    return left;
  }
  notExpr() {
    if (this.eatKw("NOT")) return { type: "not", expr: this.notExpr() };
    return this.cmpExpr();
  }
  cmpExpr() {
    const left = this.addExpr();
    let neg = false;
    if (this.isKw("NOT") && (this.isKw("IN", 1) || this.isKw("LIKE", 1) || this.isKw("BETWEEN", 1))) { this.i++; neg = true; }
    if (this.isKw("IS")) {
      this.i++;
      const negated = this.eatKw("NOT") || neg;
      this.expectKw("NULL");
      return { type: "isnull", expr: left, negated };
    }
    if (this.isKw("IN")) {
      this.i++; this.expectOp("(");
      let node;
      if (this.isKw("SELECT") || this.isKw("WITH")) {
        node = { type: "in", expr: left, subquery: this.select(), negated: neg };
      } else {
        node = { type: "in", expr: left, list: this.exprList(), negated: neg };
      }
      this.expectOp(")");
      return node;
    }
    if (this.isKw("LIKE")) {
      this.i++;
      const pattern = this.addExpr();
      return { type: "like", expr: left, pattern, negated: neg };
    }
    if (this.isKw("BETWEEN")) {
      this.i++;
      const lo = this.addExpr();
      this.expectKw("AND");
      const hi = this.addExpr();
      return { type: "between", expr: left, lo, hi, negated: neg };
    }
    if (neg) throw this.err("NOT debe ir seguido de IN, LIKE o BETWEEN.");
    const t = this.cur;
    if (t.type === "op" && ["=", "<", ">", "<=", ">=", "<>"].indexOf(t.value) !== -1) {
      this.i++;
      return { type: "bin", op: t.value, left, right: this.addExpr() };
    }
    return left;
  }
  addExpr() {
    let left = this.mulExpr();
    while (this.cur.type === "op" && ["+", "-", "||"].indexOf(this.cur.value) !== -1) {
      const op = this.cur.value; this.i++;
      left = { type: "bin", op, left, right: this.mulExpr() };
    }
    return left;
  }
  mulExpr() {
    let left = this.unaryExpr();
    while (this.cur.type === "op" && ["*", "/", "%"].indexOf(this.cur.value) !== -1) {
      const op = this.cur.value; this.i++;
      left = { type: "bin", op, left, right: this.unaryExpr() };
    }
    return left;
  }
  unaryExpr() {
    if (this.cur.type === "op" && this.cur.value === "-") { this.i++; return { type: "neg", expr: this.unaryExpr() }; }
    if (this.cur.type === "op" && this.cur.value === "+") { this.i++; return this.unaryExpr(); }
    return this.primary();
  }
  primary() {
    const t = this.cur;
    if (t.type === "number") { this.i++; return { type: "num", value: t.value }; }
    if (t.type === "string") { this.i++; return { type: "str", value: t.value }; }
    if (t.type === "op" && t.value === "*") { this.i++; return { type: "star" }; }
    if (t.type === "kw") {
      switch (t.value) {
        case "NULL": this.i++; return { type: "null" };
        case "TRUE": this.i++; return { type: "bool", value: true };
        case "FALSE": this.i++; return { type: "bool", value: false };
        case "CASE": return this.caseExpr();
        case "EXISTS": {
          this.i++; this.expectOp("(");
          const query = this.select();
          this.expectOp(")");
          return { type: "exists", subquery: query };
        }
        case "CAST": {
          this.i++; this.expectOp("(");
          const e = this.expr();
          this.expectKw("AS");
          const tyTok = this.cur;
          if (tyTok.type !== "kw" && tyTok.type !== "ident") throw this.err("CAST necesita un tipo de dato.");
          this.i++;
          const dataType = String(tyTok.value).toUpperCase();
          if (this.isOp("(")) { this.i++; while (!this.isOp(")") && this.cur.type !== "eof") this.i++; this.expectOp(")"); }
          this.expectOp(")");
          return { type: "cast", expr: e, dataType };
        }
        case "NOT": this.i++; return { type: "not", expr: this.notExpr() };
        default: break;
      }
    }
    if (t.type === "op" && t.value === "(") {
      this.i++;
      if (this.isKw("SELECT") || this.isKw("WITH")) {
        const query = this.select();
        this.expectOp(")");
        return { type: "subquery", query };
      }
      const e = this.expr();
      this.expectOp(")");
      return { type: "paren", expr: e };
    }
    if (t.type === "ident" || t.type === "kw") {
      this.i++;
      const name = t.quoted ? t.value : String(t.value).toLowerCase();
      if (this.isOp("(")) {
        this.i++;
        const fn = { type: "func", name: String(t.value).toUpperCase(), args: [] };
        if (this.isOp("*")) { this.i++; fn.star = true; }
        else if (!this.isOp(")")) {
          if (this.eatKw("DISTINCT")) fn.distinct = true;
          fn.args = this.exprList();
        }
        this.expectOp(")");
        return fn;
      }
      if (this.isOp(".")) {
        this.i++;
        const col = this.ident();
        return { type: "column", table: name, name: col.name };
      }
      return { type: "column", name };
    }
    throw this.err("Se esperaba una expresión (columna, número, texto o función).");
  }
  caseExpr() {
    this.expectKw("CASE");
    let operand = null;
    if (!this.isKw("WHEN")) operand = this.expr();
    const whens = [];
    while (this.eatKw("WHEN")) {
      const cond = this.expr();
      this.expectKw("THEN");
      const result = this.expr();
      whens.push({ cond, result });
    }
    let elseExpr = null;
    if (this.eatKw("ELSE")) elseExpr = this.expr();
    this.expectKw("END");
    return { type: "case", operand, whens, elseExpr };
  }
}

/* ============================= Utilidades de valores ============================= */

function deepClone(obj) { return JSON.parse(JSON.stringify(obj)); }
function hasOwn(obj, key) { return Object.prototype.hasOwnProperty.call(obj, key); }

/** Lectura de propiedad case-insensitive sobre filas de tablas base. */
function getCI(obj, name) {
  if (obj == null) return undefined;
  if (obj[name] !== undefined) return obj[name];
  const lower = String(name).toLowerCase();
  const keys = Object.keys(obj);
  for (let k = 0; k < keys.length; k++) {
    if (keys[k].toLowerCase() === lower) return obj[keys[k]];
  }
  return undefined;
}

/** "Limpia" artefactos de punto flotante (0.1+0.2 -> 0.3) para la UI. */
function cleanVal(v) {
  if (typeof v === "number" && isFinite(v)) return Math.round(v * 1e10) / 1e10;
  return v;
}

function toNum(v) {
  if (v === null || v === undefined) return null;
  if (typeof v === "number") return isNaN(v) ? null : v;
  if (typeof v === "boolean") return v ? 1 : 0;
  const s = String(v).trim();
  if (s === "") return null;
  const n = Number(s);
  return isNaN(n) ? null : n;
}

/** Comparación total: NULL primero; numérica si alguno es número; léxica en otro caso. */
function cmpValues(a, b) {
  let x = a; let y = b;
  const aNull = x === null || x === undefined;
  const bNull = y === null || y === undefined;
  if (aNull && bNull) return 0;
  if (aNull) return -1;
  if (bNull) return 1;
  if (typeof x === "boolean") x = x ? 1 : 0;
  if (typeof y === "boolean") y = y ? 1 : 0;
  if (typeof x === "number" || typeof y === "number") {
    const nx = toNum(x); const ny = toNum(y);
    if (nx !== null && ny !== null) return nx < ny ? -1 : nx > ny ? 1 : 0;
  }
  const sx = String(x); const sy = String(y);
  return sx < sy ? -1 : sx > sy ? 1 : 0;
}

/** Igualdad SQL: NULL = NULL es true aquí (se usa en IN / llaves de grupo / unicidad). */
function valEq(a, b) {
  const aNull = a === null || a === undefined;
  const bNull = b === null || b === undefined;
  if (aNull || bNull) return aNull && bNull;
  return cmpValues(a, b) === 0;
}

function truthy(v) {
  if (v === null || v === undefined) return false;
  if (typeof v === "boolean") return v;
  if (typeof v === "number") return v !== 0;
  if (typeof v === "string") return v.length > 0;
  return true;
}

function uniqBy(arr, keyFn) {
  const seen = new Set();
  const out = [];
  for (const x of arr) {
    const k = keyFn(x);
    if (!seen.has(k)) { seen.add(k); out.push(x); }
  }
  return out;
}

function likeToRegex(pattern) {
  let re = "^";
  for (const ch of pattern) {
    if (ch === "%") re += "[\\s\\S]*";
    else if (ch === "_") re += "[\\s\\S]";
    else re += ch.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  }
  return new RegExp(re + "$", "i");
}

/** Reconstruye SQL legible a partir de un AST de expresión (para nombrar columnas). */
function exprToSql(e) {
  if (!e || typeof e !== "object") return "?";
  switch (e.type) {
    case "num": return String(e.value);
    case "str": return "'" + String(e.value).replace(/'/g, "''") + "'";
    case "null": return "NULL";
    case "bool": return e.value ? "TRUE" : "FALSE";
    case "star": return "*";
    case "column": return e.table ? e.table + "." + e.name : e.name;
    case "paren": return "(" + exprToSql(e.expr) + ")";
    case "neg": return "-" + exprToSql(e.expr);
    case "not": return "NOT " + exprToSql(e.expr);
    case "bin": return exprToSql(e.left) + " " + e.op + " " + exprToSql(e.right);
    case "func": return e.name + "(" + (e.star ? "*" : (e.args || []).map(exprToSql).join(", ")) + ")";
    case "isnull": return exprToSql(e.expr) + (e.negated ? " IS NOT NULL" : " IS NULL");
    case "like": return exprToSql(e.expr) + (e.negated ? " NOT LIKE " : " LIKE ") + exprToSql(e.pattern);
    case "between": return exprToSql(e.expr) + " BETWEEN " + exprToSql(e.lo) + " AND " + exprToSql(e.hi);
    case "in": return exprToSql(e.expr) + (e.negated ? " NOT IN " : " IN ") + (e.subquery ? "(SELECT ...)" : "(" + (e.list || []).map(exprToSql).join(", ") + ")");
    case "subquery": return "(SELECT ...)";
    case "exists": return "EXISTS (SELECT ...)";
    case "case": return "CASE ... END";
    case "cast": return "CAST(" + exprToSql(e.expr) + " AS " + e.dataType + ")";
    default: return "expr";
  }
}

function nameOfExpr(e) {
  if (e.type === "column") return e.name;
  const s = exprToSql(e);
  return s.length > 28 ? s.slice(0, 26) + "\u2026" : s;
}

/** ¿Contiene la expresión algún agregado propio (no de subconsultas anidadas)? */
function containsAgg(node) {
  if (!node || typeof node !== "object") return false;
  if (node.type === "func" && AGGREGATES.has(node.name) && (node.star || !node.args || node.args.length <= 1)) return true;
  if (node.type === "subquery" || node.type === "exists") return false;
  if (node.type === "in" && node.subquery) return containsAgg(node.expr);
  const keys = Object.keys(node);
  for (let k = 0; k < keys.length; k++) {
    if (keys[k] === "type") continue;
    if (containsAgg(node[keys[k]])) return true;
  }
  return false;
}

/* ============================= Evaluación de expresiones ============================= */

/**
 * Resuelve una referencia a columna dentro del contexto de evaluación.
 * ctx = { row, cols:[{alias,table,name,qual}], db, group?, inWhere? }
 */
function resolveColumn(expr, ctx) {
  const row = ctx.row;
  if (!row) {
    throw new SqlError('La columna "' + (expr.table ? expr.table + "." : "") + expr.name + '" no está disponible en este contexto.',
      "Solo puedes usar columnas de las tablas indicadas en FROM (o de la tabla modificada en INSERT/UPDATE/DELETE).");
  }
  if (expr.table) {
    const qual = expr.table + "." + expr.name;
    if (hasOwn(row, qual)) return row[qual] === undefined ? null : row[qual];
    for (const c of ctx.cols) {
      if ((c.alias === expr.table || c.table === expr.table) && c.name === expr.name) {
        return row[c.qual] === undefined ? null : row[c.qual];
      }
    }
    throw new SqlError('No se encontró "' + expr.table + "." + expr.name + '".',
      "Comprueba el nombre de la tabla/alias. Alias disponibles: " + uniqBy(ctx.cols.map((c) => c.alias), (x) => x).join(", ") + ".");
  }
  const matches = ctx.cols.filter((c) => c.name === expr.name);
  if (matches.length === 1) {
    const v = row[matches[0].qual];
    return v === undefined ? null : v;
  }
  if (matches.length > 1) {
    throw new SqlError('La columna "' + expr.name + '" es ambigua: existe en ' + matches.map((m) => m.alias).join(" y en ") + ".",
      "Califícala con su tabla o alias, por ejemplo: " + matches[0].alias + "." + expr.name + ".");
  }
  const avail = uniqBy(ctx.cols.map((c) => c.name), (x) => x);
  throw new SqlError('No existe la columna "' + expr.name + '".',
    "Columnas disponibles: " + (avail.length ? avail.slice(0, 14).join(", ") : "ninguna (la consulta no tiene FROM)") + ".");
}

function evalExpr(expr, ctx) {
  switch (expr.type) {
    case "num": return expr.value;
    case "str": return expr.value;
    case "null": return null;
    case "bool": return expr.value ? 1 : 0;
    case "star": throw new SqlError("El operador * solo puede usarse dentro de COUNT(*).");
    case "column": return resolveColumn(expr, ctx);
    case "paren": return evalExpr(expr.expr, ctx);
    case "neg": {
      const v = evalExpr(expr.expr, ctx);
      if (v === null || v === undefined) return null;
      const num = toNum(v);
      return num === null ? null : -num;
    }
    case "not": return truthy(evalExpr(expr.expr, ctx)) ? 0 : 1;
    case "bin": return evalBin(expr, ctx);
    case "like": {
      const v = evalExpr(expr.expr, ctx);
      const p = evalExpr(expr.pattern, ctx);
      if (v === null || v === undefined || p === null || p === undefined) return null;
      const matched = likeToRegex(String(p)).test(String(v));
      return expr.negated ? !matched : matched;
    }
    case "in": {
      const v = evalExpr(expr.expr, ctx);
      let list;
      if (expr.subquery) {
        const res = execSelect(expr.subquery, ctx.db);
        if (res.columns.length > 1) throw new SqlError("La subconsulta de IN debe devolver una sola columna.");
        list = res.rows.map((r) => r[0]);
      } else {
        list = expr.list.map((e) => evalExpr(e, ctx));
      }
      if (v === null || v === undefined) return null;
      const found = list.some((x) => valEq(v, x));
      return expr.negated ? !found : found;
    }
    case "between": {
      const v = evalExpr(expr.expr, ctx);
      const lo = evalExpr(expr.lo, ctx);
      const hi = evalExpr(expr.hi, ctx);
      if (v === null || lo === null || hi === null || v === undefined || lo === undefined || hi === undefined) return null;
      const inside = cmpValues(v, lo) >= 0 && cmpValues(v, hi) <= 0;
      return expr.negated ? !inside : inside;
    }
    case "isnull": {
      const v = evalExpr(expr.expr, ctx);
      const isNull = v === null || v === undefined;
      return expr.negated ? !isNull : isNull;
    }
    case "exists": {
      const res = execSelect(expr.subquery, ctx.db);
      return res.rows.length > 0 ? 1 : 0;
    }
    case "subquery": {
      const res = execSelect(expr.query, ctx.db);
      if (res.rows.length > 1) {
        throw new SqlError("La subconsulta devolvió " + res.rows.length + " filas, pero se usó como valor único.",
          "Si esperas varias filas, usa IN (SELECT ...) o un JOIN en lugar de una subconsulta escalar.");
      }
      if (res.rows.length === 0) return null;
      return res.rows[0][0];
    }
    case "func": return evalFunc(expr, ctx);
    case "case": {
      if (expr.operand) {
        const operandVal = evalExpr(expr.operand, ctx);
        for (const w of expr.whens) {
          if (valEq(operandVal, evalExpr(w.cond, ctx))) return evalExpr(w.result, ctx);
        }
      } else {
        for (const w of expr.whens) {
          if (truthy(evalExpr(w.cond, ctx))) return evalExpr(w.result, ctx);
        }
      }
      return expr.elseExpr ? evalExpr(expr.elseExpr, ctx) : null;
    }
    case "cast": {
      const v = evalExpr(expr.expr, ctx);
      if (v === null || v === undefined) return null;
      const ty = expr.dataType;
      if (ty.indexOf("INT") !== -1) return Math.trunc(toNum(v) || 0);
      if (ty.indexOf("CHAR") !== -1 || ty.indexOf("TEXT") !== -1 || ty.indexOf("CLOB") !== -1) return String(v);
      if (ty.indexOf("REAL") !== -1 || ty.indexOf("FLOA") !== -1 || ty.indexOf("DOUB") !== -1) return toNum(v);
      if (ty.indexOf("NUM") !== -1 || ty.indexOf("DEC") !== -1) return toNum(v);
      return String(v);
    }
    default:
      throw new SqlError("Expresión no soportada (" + expr.type + ").");
  }
}

/** Lógica ternaria de SQL para AND/OR; aritmética con coerción numérica. */
function evalBin(expr, ctx) {
  const op = expr.op;
  if (op === "AND" || op === "OR") {
    const l = evalExpr(expr.left, ctx);
    const r = evalExpr(expr.right, ctx);
    const lt = truthy(l); const rt = truthy(r);
    const lNull = l === null || l === undefined;
    const rNull = r === null || r === undefined;
    if (op === "AND") {
      if (lt && rt) return 1;
      if (!lt && !lNull) return 0;
      if (!rt && !rNull) return 0;
      return null;
    }
    if (lt || rt) return 1;
    if (lNull || rNull) return null;
    return 0;
  }
  const a = evalExpr(expr.left, ctx);
  const b = evalExpr(expr.right, ctx);
  switch (op) {
    case "=": if (a === null || a === undefined || b === null || b === undefined) return null; return valEq(a, b);
    case "<>": if (a === null || a === undefined || b === null || b === undefined) return null; return !valEq(a, b);
    case "<": case "<=": case ">": case ">=": {
      if (a === null || a === undefined || b === null || b === undefined) return null;
      const c = cmpValues(a, b);
      if (op === "<") return c < 0;
      if (op === "<=") return c <= 0;
      if (op === ">") return c > 0;
      return c >= 0;
    }
    case "||": {
      if (a === null || a === undefined || b === null || b === undefined) return null;
      return String(a) + String(b);
    }
    default: {
      if (a === null || a === undefined || b === null || b === undefined) return null;
      const na = toNum(a) || 0; const nb = toNum(b) || 0;
      if ((op === "/" || op === "%") && nb === 0) return null; // división por cero -> NULL (como SQLite)
      if (op === "+") return na + nb;
      if (op === "-") return na - nb;
      if (op === "*") return na * nb;
      if (op === "/") return na / nb;
      return na % nb;
    }
  }
}

function evalFunc(expr, ctx) {
  const name = expr.name;
  const isAggUse = AGGREGATES.has(name) && (expr.star || (expr.args && expr.args.length <= 1));
  if (isAggUse) {
    if (!ctx.group) {
      if (ctx.inWhere) {
        throw new SqlError("No puedes usar la función de agregado " + name + "() dentro de WHERE.",
          "WHERE filtra fila a fila. Para filtrar por agregados usa HAVING, p. ej. GROUP BY x HAVING COUNT(*) > 2.");
      }
      throw new SqlError("La función de agregado " + name + "() no puede usarse en este contexto.",
        "Los agregados se evalúan en la lista de SELECT, en HAVING o en ORDER BY.");
    }
    const rows = ctx.group;
    const rowCtxBase = { cols: ctx.cols, db: ctx.db, group: null };
    if (name === "COUNT") {
      if (expr.star) return rows.length;
      const cvals = rows.map((r) => evalExpr(expr.args[0], Object.assign({}, rowCtxBase, { row: r })))
        .filter((v) => v !== null && v !== undefined);
      if (expr.distinct) return uniqBy(cvals, (v) => JSON.stringify(v)).length;
      return cvals.length;
    }
    let vals = rows.map((r) => evalExpr(expr.args[0], Object.assign({}, rowCtxBase, { row: r })))
      .filter((v) => v !== null && v !== undefined);
    if (expr.distinct) vals = uniqBy(vals, (v) => JSON.stringify(v));
    if (name === "SUM") {
      if (!vals.length) return null;
      return vals.reduce((acc, v) => acc + (toNum(v) || 0), 0);
    }
    if (name === "AVG") {
      const nums = vals.map((v) => toNum(v)).filter((v) => v !== null);
      if (!nums.length) return null;
      return nums.reduce((acc, v) => acc + v, 0) / nums.length;
    }
    if (!vals.length) return null;
    let best = vals[0];
    for (const v of vals) {
      const c = cmpValues(v, best);
      if (name === "MIN" ? c < 0 : c > 0) best = v;
    }
    return best;
  }

  const args = (expr.args || []).map((a) => evalExpr(a, ctx));
  switch (name) {
    case "MAX": case "MIN": {
      const vs = args.filter((v) => v !== null && v !== undefined);
      if (!vs.length) return null;
      let best = vs[0];
      for (const v of vs) {
        const c = cmpValues(v, best);
        if (name === "MIN" ? c < 0 : c > 0) best = v;
      }
      return best;
    }
    case "UPPER": return args[0] === null || args[0] === undefined ? null : String(args[0]).toUpperCase();
    case "LOWER": return args[0] === null || args[0] === undefined ? null : String(args[0]).toLowerCase();
    case "LENGTH": return args[0] === null || args[0] === undefined ? null : String(args[0]).length;
    case "TRIM": return args[0] === null || args[0] === undefined ? null : String(args[0]).trim();
    case "ABS": return args[0] === null || args[0] === undefined ? null : Math.abs(toNum(args[0]) || 0);
    case "ROUND": {
      if (args[0] === null || args[0] === undefined) return null;
      const digits = args.length > 1 ? (toNum(args[1]) || 0) : 0;
      const f = Math.pow(10, digits);
      return Math.round((toNum(args[0]) || 0) * f) / f;
    }
    case "COALESCE": {
      for (const a of args) if (a !== null && a !== undefined) return a;
      return null;
    }
    case "IFNULL": return args[0] === null || args[0] === undefined ? args[1] : args[0];
    case "NULLIF": return valEq(args[0], args[1]) ? null : args[0];
    case "REPLACE": {
      if (args[0] === null || args[0] === undefined || args[1] === null || args[1] === undefined) return null;
      return String(args[0]).split(String(args[1])).join(args[2] === null || args[2] === undefined ? "" : String(args[2]));
    }
    case "SUBSTR": case "SUBSTRING": {
      if (args[0] === null || args[0] === undefined) return null;
      const s = String(args[0]);
      let start = toNum(args[1]);
      if (start === null) start = 1;
      if (start > 0) start -= 1;
      else if (start < 0) start = Math.max(0, s.length + start);
      if (args.length > 2 && args[2] !== null && args[2] !== undefined) {
        return s.slice(start, start + Math.max(0, toNum(args[2]) || 0));
      }
      return s.slice(start);
    }
    default:
      throw new SqlError("Función desconocida: " + name + "().",
        "Funciones disponibles: COUNT, SUM, AVG, MIN, MAX, UPPER, LOWER, LENGTH, ROUND, ABS, COALESCE, IFNULL, NULLIF, REPLACE, SUBSTR, TRIM y CAST(... AS ...).");
  }
}

/* ============================= Ejecución de consultas ============================= */

function tableNames(db) { return Object.keys(db.tables); }

function getTable(db, name) {
  if (hasOwn(db.tables, name)) return db.tables[name];
  const lower = String(name).toLowerCase();
  const keys = Object.keys(db.tables);
  for (const k of keys) if (k.toLowerCase() === lower) return db.tables[k];
  return null;
}

/** Carga una referencia de FROM (tabla física o subconsulta) como fuente de filas. */
function loadSource(ref, db) {
  if (ref.type === "table") {
    const tbl = getTable(db, ref.name);
    if (!tbl) {
      throw new SqlError('No existe la tabla "' + ref.name + '".',
        "Tablas disponibles en esta base de datos: " + tableNames(db).join(", ") + ". Puedes verlas en la pestaña Esquema.");
    }
    return { alias: ref.alias, table: ref.name, columns: tbl.columns.map((c) => c.name), rows: tbl.rows };
  }
  const res = execSelect(ref.query, db);
  const cols = res.columns.map((c, idx) => (c && String(c).trim() ? String(c) : "col_" + (idx + 1)));
  const rows = res.rows.map((r) => {
    const o = {};
    cols.forEach((c, idx) => { o[c] = r[idx]; });
    return o;
  });
  return { alias: ref.alias, table: ref.alias, columns: cols, rows };
}

/** Construye el producto de FROM + JOINs. Las filas internas usan claves "alias.columna". */
function buildFrom(node, db) {
  if (!node.from) return { rows: [{}], cols: [] };
  const first = loadSource(node.from, db);
  const cols = [];
  const addCols = (src) => {
    if (cols.some((c) => c.alias === src.alias)) {
      throw new SqlError('El alias "' + src.alias + '" se usa más de una vez en FROM.',
        "Asigna un alias distinto a cada tabla o subconsulta.");
    }
    src.columns.forEach((cn) => cols.push({ alias: src.alias, table: src.table, name: String(cn).toLowerCase(), qual: src.alias + "." + String(cn).toLowerCase() }));
  };
  const qualify = (src, rawRow) => {
    const o = {};
    src.columns.forEach((cn) => {
      const v = getCI(rawRow, cn);
      o[src.alias + "." + String(cn).toLowerCase()] = v === undefined ? null : v;
    });
    return o;
  };

  addCols(first);
  let rows = first.rows.map((r) => qualify(first, r));

  for (const j of node.joins || []) {
    const right = loadSource(j.ref, db);
    const leftQuals = cols.map((c) => c.qual);
    addCols(right);
    const rrows = right.rows.map((r) => qualify(right, r));
    if (rows.length * rrows.length > MAX_JOIN_PAIRS) {
      throw new SqlError("El JOIN generaría " + (rows.length * rrows.length) + " combinaciones (máximo " + MAX_JOIN_PAIRS + ").",
        "Añade una condición ON/WHERE más selectiva o limita el tamaño de las tablas implicadas.");
    }
    const rightQuals = right.columns.map((cn) => right.alias + "." + String(cn).toLowerCase());
    const out = [];
    const matchedRight = new Set();
    for (const l of rows) {
      let matched = false;
      for (let ri = 0; ri < rrows.length; ri++) {
        const merged = Object.assign({}, l, rrows[ri]);
        if (j.joinType === "cross" || !j.on || truthy(evalExpr(j.on, { row: merged, cols, db }))) {
          out.push(merged);
          matched = true;
          matchedRight.add(ri);
        }
      }
      if (!matched && (j.joinType === "left" || j.joinType === "full")) {
        const merged = Object.assign({}, l);
        rightQuals.forEach((q) => { merged[q] = null; });
        out.push(merged);
      }
    }
    if (j.joinType === "right" || j.joinType === "full") {
      for (let ri = 0; ri < rrows.length; ri++) {
        if (!matchedRight.has(ri)) {
          const merged = Object.assign({}, rrows[ri]);
          leftQuals.forEach((q) => { merged[q] = null; });
          out.push(merged);
        }
      }
    }
    rows = out;
  }
  return { rows, cols };
}

/** Convierte un resultado {columns, rows(arrays)} en una tabla física del sandbox. */
function resultToTable(res) {
  const used = {};
  const columns = res.columns.map((c, i) => {
    let name = c && String(c).trim() ? String(c) : "col_" + (i + 1);
    const base = name.toLowerCase();
    if (used[base]) { used[base] += 1; name = base + "_" + used[base]; } else { used[base] = 1; }
    let type = "TEXT";
    for (const r of res.rows) {
      if (typeof r[i] === "number") { type = "NUMERIC"; break; }
    }
    return { name, type, notNull: false, primaryKey: false, unique: false, defaultValue: null, autoincrement: false };
  });
  const rows = res.rows.map((r) => {
    const o = {};
    columns.forEach((c, i) => { const v = cleanVal(r[i]); o[c.name] = v === undefined ? null : v; });
    return o;
  });
  return { columns, rows };
}

/** Ejecuta un SELECT (incluye WITH y operaciones de conjunto). Devuelve {columns, rows, truncated}. */
function execSelect(node, db) {
  if (node.type === "with") {
    const db2 = { name: db.name, tables: Object.assign({}, db.tables) };
    for (const cte of node.ctes) {
      const res = execSelect(cte.query, db2);
      db2.tables[cte.name] = resultToTable(res);
    }
    return execSelect(node.main, db2);
  }
  if (node.type === "setop") {
    const left = execSelect(node.left, db);
    const right = execSelect(node.right, db);
    const keyOf = (r) => JSON.stringify(r.map((v) => (v === undefined ? null : v)));
    let rows;
    if (node.op === "UNION") {
      rows = node.all ? left.rows.concat(right.rows) : uniqBy(left.rows.concat(right.rows), keyOf);
    } else if (node.op === "INTERSECT") {
      const set = new Set(right.rows.map(keyOf));
      rows = uniqBy(left.rows.filter((r) => set.has(keyOf(r))), keyOf);
    } else {
      const set = new Set(right.rows.map(keyOf));
      rows = uniqBy(left.rows.filter((r) => !set.has(keyOf(r))), keyOf);
    }
    return { columns: left.columns, rows, truncated: false };
  }

  const from = buildFrom(node, db);
  const baseCtx = { cols: from.cols, db };
  let rows = from.rows;

  if (node.where) {
    const wctx = Object.assign({}, baseCtx, { inWhere: true, group: null });
    rows = rows.filter((r) => truthy(evalExpr(node.where, Object.assign({}, wctx, { row: r }))));
  }

  const hasAgg = node.items.some((it) => !it.star && containsAgg(it.expr)) || (node.having ? containsAgg(node.having) : false);
  const grouped = !!node.groupBy || hasAgg;

  const outCols = [];
  for (const it of node.items) {
    if (it.star) from.cols.forEach((c) => outCols.push(c.name));
    else outCols.push(it.alias || nameOfExpr(it.expr));
  }

  const computeVals = (evaluator) => {
    const vals = [];
    for (const it of node.items) {
      if (it.star) {
        for (const c of from.cols) vals.push(evaluator({ type: "column", table: c.alias, name: c.name }));
      } else {
        vals.push(evaluator(it.expr));
      }
    }
    return vals;
  };

  let outRows = [];
  if (grouped) {
    const groups = [];
    if (node.groupBy) {
      const map = new Map();
      for (const r of rows) {
        const keyVals = node.groupBy.map((g) => evalExpr(g, Object.assign({}, baseCtx, { row: r })));
        const k = JSON.stringify(keyVals.map((v) => (v === undefined ? null : v)));
        if (!map.has(k)) map.set(k, []);
        map.get(k).push(r);
      }
      for (const gRows of map.values()) groups.push(gRows);
    } else {
      groups.push(rows);
    }
    for (const gRows of groups) {
      const gctx = Object.assign({}, baseCtx, { group: gRows, row: gRows[0] || {} });
      if (node.having && !truthy(evalExpr(node.having, gctx))) continue;
      outRows.push({ vals: computeVals((e) => evalExpr(e, gctx)), src: gRows[0] || {}, group: gRows });
    }
  } else {
    for (const r of rows) {
      const rctx = Object.assign({}, baseCtx, { row: r, group: null });
      outRows.push({ vals: computeVals((e) => evalExpr(e, rctx)), src: r, group: null });
    }
  }

  if (node.distinct) {
    outRows = uniqBy(outRows, (o) => JSON.stringify(o.vals.map((v) => (v === undefined ? null : v))));
  }

  if (node.orderBy && node.orderBy.length) {
    const accessors = node.orderBy.map((ob) => {
      if (ob.expr.type === "num") {
        const idx = ob.expr.value - 1;
        if (idx < 0 || idx >= outCols.length) throw new SqlError("ORDER BY " + ob.expr.value + ": no hay columna de salida con ese número.", "Los números en ORDER BY son posiciones (empezando en 1).");
        return { kind: "index", idx };
      }
      if (ob.expr.type === "column" && !ob.expr.table) {
        const idx = outCols.findIndex((c) => String(c).toLowerCase() === ob.expr.name);
        if (idx >= 0) return { kind: "index", idx };
      }
      return { kind: "expr", expr: ob.expr };
    });
    outRows.sort((A, B) => {
      for (let k = 0; k < accessors.length; k++) {
        const acc = accessors[k];
        const dir = node.orderBy[k].dir === "desc" ? -1 : 1;
        let va; let vb;
        if (acc.kind === "index") { va = A.vals[acc.idx]; vb = B.vals[acc.idx]; }
        else {
          va = evalExpr(acc.expr, Object.assign({}, baseCtx, { row: A.src, group: A.group || undefined }));
          vb = evalExpr(acc.expr, Object.assign({}, baseCtx, { row: B.src, group: B.group || undefined }));
        }
        const c = cmpValues(va, vb);
        if (c !== 0) return c * dir;
      }
      return 0;
    });
  }

  let start = 0;
  let end = outRows.length;
  if (node.offset !== undefined && node.offset !== null) start = Math.max(0, node.offset);
  if (node.limit !== undefined && node.limit !== null) end = Math.min(outRows.length, start + node.limit);
  const sliced = outRows.slice(start, Math.max(start, end));
  let truncated = false;
  let finalRows = sliced.map((o) => o.vals.map(cleanVal));
  if (finalRows.length > MAX_ROWS) { finalRows = finalRows.slice(0, MAX_ROWS); truncated = true; }
  return { columns: outCols, rows: finalRows, truncated };
}

/* ============================= DML / DDL / Transacciones ============================= */

function nextAutoId(tbl, colName) {
  let max = 0;
  for (const r of tbl.rows) {
    const v = toNum(getCI(r, colName));
    if (v !== null && Number.isInteger(v) && v > max) max = v;
  }
  return max + 1;
}

/** Inserta una fila ya construida {columna: valor} aplicando defaults y restricciones. */
function insertRowIntoTable(tbl, tableName, partialRow, db) {
  const row = {};
  for (const cdef of tbl.columns) {
    let v = partialRow[cdef.name];
    if (v === undefined) v = getCI(partialRow, cdef.name);
    if (v === undefined) {
      if (cdef.defaultValue !== null && cdef.defaultValue !== undefined) {
        v = evalExpr(cdef.defaultValue, { row: null, cols: [], db });
      } else if (cdef.autoincrement || (cdef.primaryKey && String(cdef.type).toUpperCase().indexOf("INT") !== -1)) {
        v = nextAutoId(tbl, cdef.name);
      } else {
        v = null;
      }
    }
    if (cdef.notNull && (v === null || v === undefined)) {
      throw new SqlError('INSERT en "' + tableName + '": la columna "' + cdef.name + '" no puede ser NULL (NOT NULL).',
        'Incluye un valor para "' + cdef.name + '" en la lista de columnas del INSERT.');
    }
    if ((cdef.primaryKey || cdef.unique) && v !== null && v !== undefined) {
      if (tbl.rows.some((r) => valEq(getCI(r, cdef.name), v))) {
        throw new SqlError('INSERT en "' + tableName + '": el valor ' + JSON.stringify(v) + ' ya existe en "' + cdef.name + '" (clave única/primaria).',
          "Usa otro valor u omite la columna si es autoincremental.");
      }
    }
    row[cdef.name] = v === undefined ? null : v;
  }
  tbl.rows.push(row);
}

function execInsert(stmt, db) {
  const tbl = getTable(db, stmt.table);
  if (!tbl) {
    throw new SqlError('No existe la tabla "' + stmt.table + '".', "Tablas disponibles: " + tableNames(db).join(", ") + ".");
  }
  const colNames = stmt.columns ? stmt.columns.slice() : tbl.columns.map((c) => c.name);
  for (const cn of colNames) {
    if (!tbl.columns.some((tc) => tc.name.toLowerCase() === String(cn).toLowerCase())) {
      throw new SqlError('La tabla "' + stmt.table + '" no tiene la columna "' + cn + '".',
        "Columnas válidas: " + tbl.columns.map((c) => c.name).join(", ") + ".");
    }
  }
  const realName = (cn) => tbl.columns.find((tc) => tc.name.toLowerCase() === String(cn).toLowerCase()).name;
  let count = 0;
  if (stmt.select) {
    const res = execSelect(stmt.select, db);
    if (res.columns.length !== colNames.length) {
      throw new SqlError("INSERT ... SELECT: el SELECT devuelve " + res.columns.length + " columnas pero la lista de destino tiene " + colNames.length + ".",
        "Ajusta las columnas del SELECT a las del INSERT.");
    }
    for (const r of res.rows) {
      const partial = {};
      colNames.forEach((cn, idx) => { partial[realName(cn)] = r[idx]; });
      insertRowIntoTable(tbl, stmt.table, partial, db);
      count++;
    }
  } else {
    for (const vals of stmt.valuesList) {
      if (vals.length !== colNames.length) {
        throw new SqlError("INSERT: se esperaban " + colNames.length + " valores pero se indican " + vals.length + ".",
          "Revisa que la lista de columnas y la de VALUES tengan el mismo tamaño.");
      }
      const partial = {};
      vals.forEach((v, idx) => { partial[realName(colNames[idx])] = evalExpr(v, { row: null, cols: [], db }); });
      insertRowIntoTable(tbl, stmt.table, partial, db);
      count++;
    }
  }
  return { kind: "message", message: count + ' fila(s) insertada(s) en "' + stmt.table + '".', affected: count, table: stmt.table };
}

function execUpdate(stmt, db) {
  const tbl = getTable(db, stmt.table);
  if (!tbl) throw new SqlError('No existe la tabla "' + stmt.table + '".', "Tablas disponibles: " + tableNames(db).join(", ") + ".");
  const alias = stmt.alias || stmt.table;
  const cols = tbl.columns.map((c) => ({ alias, table: stmt.table, name: c.name.toLowerCase(), qual: alias + "." + c.name.toLowerCase() }));
  for (const a of stmt.assigns) {
    if (!cols.some((c) => c.name === String(a.column).toLowerCase())) {
      throw new SqlError('La tabla "' + stmt.table + '" no tiene la columna "' + a.column + '".',
        "Columnas válidas: " + tbl.columns.map((c) => c.name).join(", ") + ".");
    }
  }
  let count = 0;
  for (const r of tbl.rows) {
    const work = {};
    cols.forEach((c) => { const v = getCI(r, c.name); work[c.qual] = v === undefined ? null : v; });
    const ctx = { row: work, cols, db, group: null, inWhere: true };
    if (stmt.where && !truthy(evalExpr(stmt.where, ctx))) continue;
    const newVals = stmt.assigns.map((a) => ({ col: String(a.column).toLowerCase(), val: evalExpr(a.expr, ctx) }));
    for (const nv of newVals) {
      const cdef = tbl.columns.find((c) => c.name.toLowerCase() === nv.col);
      if (cdef.notNull && (nv.val === null || nv.val === undefined)) {
        throw new SqlError('UPDATE en "' + stmt.table + '": la columna "' + cdef.name + '" no puede ser NULL.');
      }
      if ((cdef.primaryKey || cdef.unique) && nv.val !== null && nv.val !== undefined) {
        const current = work[alias + "." + nv.col];
        if (!valEq(current, nv.val) && tbl.rows.some((other) => other !== r && valEq(getCI(other, cdef.name), nv.val))) {
          throw new SqlError('UPDATE en "' + stmt.table + '": el valor ' + JSON.stringify(nv.val) + ' ya existe en "' + cdef.name + '" (clave única).');
        }
      }
    }
    for (const nv of newVals) {
      const cdef = tbl.columns.find((c) => c.name.toLowerCase() === nv.col);
      r[cdef.name] = nv.val === undefined ? null : nv.val;
    }
    count++;
  }
  const res = { kind: "message", message: count + ' fila(s) actualizada(s) en "' + stmt.table + '".', affected: count, table: stmt.table };
  if (!stmt.where) res.warning = "Ojo: tu UPDATE no tenía WHERE y ha modificado TODAS las filas de la tabla.";
  return res;
}

function execDelete(stmt, db) {
  const tbl = getTable(db, stmt.table);
  if (!tbl) throw new SqlError('No existe la tabla "' + stmt.table + '".', "Tablas disponibles: " + tableNames(db).join(", ") + ".");
  const alias = stmt.alias || stmt.table;
  const cols = tbl.columns.map((c) => ({ alias, table: stmt.table, name: c.name.toLowerCase(), qual: alias + "." + c.name.toLowerCase() }));
  const kept = [];
  let count = 0;
  for (const r of tbl.rows) {
    const work = {};
    cols.forEach((c) => { const v = getCI(r, c.name); work[c.qual] = v === undefined ? null : v; });
    if (stmt.where && !truthy(evalExpr(stmt.where, { row: work, cols, db, group: null, inWhere: true }))) kept.push(r);
    else count++;
  }
  tbl.rows = kept;
  const res = { kind: "message", message: count + ' fila(s) eliminada(s) de "' + stmt.table + '".', affected: count, table: stmt.table };
  if (!stmt.where) res.warning = 'Ojo: tu DELETE no tenía WHERE y ha vaciado TODA la tabla. Puedes restaurarla con "Reiniciar BD".';
  return res;
}

function execCreate(stmt, db) {
  if (getTable(db, stmt.name)) {
    if (stmt.ifNotExists) return { kind: "message", message: 'La tabla "' + stmt.name + '" ya existe (IF NOT EXISTS: se omite).' };
    throw new SqlError('La tabla "' + stmt.name + '" ya existe.', "Usa CREATE TABLE IF NOT EXISTS u otro nombre.");
  }
  if (stmt.asSelect) {
    db.tables[stmt.name] = resultToTable(execSelect(stmt.asSelect, db));
    return { kind: "message", message: 'Tabla "' + stmt.name + '" creada a partir del SELECT (' + db.tables[stmt.name].rows.length + " filas)." };
  }
  const seen = {};
  for (const c of stmt.columns) {
    if (seen[c.name]) throw new SqlError('La columna "' + c.name + '" está repetida en CREATE TABLE.');
    seen[c.name] = true;
  }
  db.tables[stmt.name] = { columns: deepClone(stmt.columns), rows: [] };
  return { kind: "message", message: 'Tabla "' + stmt.name + '" creada con ' + stmt.columns.length + " columna(s)." };
}

function execDrop(stmt, db) {
  const tbl = getTable(db, stmt.name);
  if (!tbl) {
    if (stmt.ifExists) return { kind: "message", message: 'La tabla "' + stmt.name + '" no existe (IF EXISTS: se omite).' };
    throw new SqlError('No existe la tabla "' + stmt.name + '".', "Tablas disponibles: " + tableNames(db).join(", ") + ".");
  }
  const realKey = Object.keys(db.tables).find((k) => k.toLowerCase() === stmt.name.toLowerCase()) || stmt.name;
  delete db.tables[realKey];
  return { kind: "message", message: 'Tabla "' + stmt.name + '" eliminada.' };
}

/** Ejecuta una sentencia ya parseada sobre la db (la muta en DML/DDL). */
function execStatement(db, stmt) {
  switch (stmt.type) {
    case "select": case "with": case "setop": {
      const res = execSelect(stmt, db);
      return { kind: "rows", columns: res.columns, rows: res.rows, truncated: res.truncated, rowCount: res.rows.length };
    }
    case "insert": return execInsert(stmt, db);
    case "update": return execUpdate(stmt, db);
    case "delete": return execDelete(stmt, db);
    case "create": return execCreate(stmt, db);
    case "drop": return execDrop(stmt, db);
    case "begin": {
      if (db.__tx) throw new SqlError("Ya hay una transacción abierta.", "Ciérrala con COMMIT; (guardar) o ROLLBACK; (deshacer) antes de iniciar otra.");
      db.__tx = deepClone(db.tables);
      return { kind: "message", message: "Transacción iniciada (BEGIN). Los cambios son provisionales." };
    }
    case "commit": {
      if (!db.__tx) throw new SqlError("No hay ninguna transacción abierta.", "Inicia una con BEGIN; antes de COMMIT;.");
      db.__tx = null;
      return { kind: "message", message: "Cambios confirmados (COMMIT). Ya son permanentes." };
    }
    case "rollback": {
      if (!db.__tx) throw new SqlError("No hay ninguna transacción abierta que revertir.", "Inicia una con BEGIN; antes de ROLLBACK;.");
      db.tables = db.__tx;
      db.__tx = null;
      return { kind: "message", message: "Transacción revertida (ROLLBACK): se deshicieron los cambios posteriores a BEGIN." };
    }
    default:
      throw new SqlError("Sentencia no soportada por el motor: " + stmt.type + ".");
  }
}

/* ============================= Capa de validación/seguridad ============================= */

function hasStatementStart(kw) {
  return ["SELECT", "WITH", "INSERT", "UPDATE", "DELETE", "CREATE", "DROP", "BEGIN", "COMMIT", "ROLLBACK"].indexOf(kw) !== -1;
}

/**
 * Valida y parsea un script SQL completo SIN ejecutarlo.
 * Rechaza: vacío, exceso de longitud/sentencias, keywords peligrosas y
 * cualquier sentencia fuera de la lista blanca.
 */
function validateScript(sql) {
  if (typeof sql !== "string") throw new SqlError("La consulta debe ser un texto.");
  const trimmed = sql.trim();
  if (!trimmed || /^(-{2}[^\n]*\n?|\s|\/\*[\s\S]*?\*\/)+$/.test(sql)) {
    throw new SqlError("El editor está vacío (o solo contiene comentarios).",
      "Escribe una sentencia, por ejemplo: SELECT * FROM clientes;");
  }
  if (trimmed.length > MAX_SQL_LENGTH) {
    throw new SqlError("La consulta supera el máximo de " + MAX_SQL_LENGTH + " caracteres.");
  }
  const tokens = tokenize(sql);
  for (const tk of tokens) {
    if (tk.type === "kw" || tk.type === "ident") {
      const up = String(tk.value).toUpperCase();
      if (FORBIDDEN_WORDS.has(up)) {
        throw new SqlError('La instrucción "' + up + '" no está permitida en este entorno.',
          "El sandbox solo admite SQL estándar (SELECT, INSERT, UPDATE, DELETE, CREATE, DROP, WITH, BEGIN/COMMIT/ROLLBACK) sobre las bases de datos de ejemplo.");
      }
    }
  }
  const streams = [];
  let cur = [];
  for (const tk of tokens) {
    if (tk.type === "comment") continue;
    if (tk.type === "op" && tk.value === ";") { if (cur.length) streams.push(cur); cur = []; }
    else cur.push(tk);
  }
  if (cur.length) streams.push(cur);
  if (!streams.length) throw new SqlError("No hay ninguna sentencia SQL que ejecutar.", "Escribe por ejemplo: SELECT 1 + 1;");
  if (streams.length > MAX_STATEMENTS) throw new SqlError("Demasiadas sentencias seguidas (máximo " + MAX_STATEMENTS + ").");
  const statements = streams.map((stream) => {
    const first = stream[0];
    if (first.type !== "kw" || !hasStatementStart(first.value)) {
      throw new SqlError('Sentencia no permitida: "' + (first.raw || first.value) + '".',
        "Lista blanca: SELECT, WITH, INSERT, UPDATE, DELETE, CREATE TABLE, DROP TABLE, BEGIN, COMMIT, ROLLBACK.");
    }
    const p = new Parser(stream.concat([{ type: "eof", value: null, pos: first.pos, end: first.pos, raw: "" }]));
    const st = p.parseProgram();
    if (st.length !== 1) throw new SqlError('Cada bloque entre ";" debe contener una única sentencia.');
    return st[0];
  });
  return { statements, tokens };
}

function now() {
  if (typeof performance !== "undefined" && performance.now) return performance.now();
  return Date.now();
}

/**
 * Punto de entrada principal: valida + ejecuta el script sobre la db dada.
 * NUNCA lanza: todo error se devuelve serializado en `error`.
 * @returns {{ok:boolean, results:Array, messages:Array, error:({message:string,hint:string|null}|null), ms:number}}
 */
function executeScript(db, sql) {
  const t0 = now();
  const results = [];
  const messages = [];
  let error = null;
  try {
    const validated = validateScript(sql);
    for (const stmt of validated.statements) {
      const r = execStatement(db, stmt);
      if (!r) continue;
      if (r.kind === "rows") {
        results.push({ kind: "rows", columns: r.columns, rows: r.rows, rowCount: r.rowCount, truncated: r.truncated });
        if (r.truncated) messages.push({ type: "warning", text: "Resultado limitado a " + MAX_ROWS + " filas. Añade LIMIT para acotarlo." });
      } else {
        messages.push({ type: "success", text: r.message });
        if (r.warning) messages.push({ type: "warning", text: r.warning });
      }
    }
  } catch (e) {
    if (e instanceof SqlError) error = { message: e.message, hint: e.hint };
    else error = { message: "Error interno del motor: " + (e && e.message ? e.message : String(e)), hint: "Simplifica la consulta e inténtalo de nuevo." };
  }
  return { ok: error === null, results, messages, error, ms: Math.round((now() - t0) * 100) / 100 };
}

/* ============================= Bases de datos de ejemplo (seeds) ============================= */

/** Construye una tabla {columns, rows} a partir de definiciones y filas en array. */
function makeTable(colDefs, rowsArr) {
  const columns = colDefs.map((d) => Object.assign({ name: d[0], type: d[1], notNull: false, primaryKey: false, unique: false, defaultValue: null, autoincrement: false }, d[2] || {}));
  const rows = rowsArr.map((r) => {
    const o = {};
    columns.forEach((c, i) => { o[c.name] = i < r.length ? r[i] : null; });
    return o;
  });
  return { columns, rows };
}

const PK = { primaryKey: true, notNull: true, autoincrement: true };
const NN = { notNull: true };

function seedTienda() {
  return {
    clientes: makeTable(
      [["id", "INTEGER", PK], ["nombre", "TEXT", NN], ["ciudad", "TEXT"], ["email", "TEXT"], ["fecha_registro", "TEXT"]],
      [
        [1, "Ana García", "Madrid", "ana@example.com", "2022-01-15"],
        [2, "Luis Martínez", "Barcelona", "luis@example.com", "2022-03-22"],
        [3, "María López", "Madrid", "maria@example.com", "2022-07-01"],
        [4, "Carlos Ruiz", "Valencia", "carlos@example.com", "2023-01-10"],
        [5, "Laura Sánchez", "Sevilla", "laura@example.com", "2023-05-30"],
        [6, "Pedro Gómez", "Bilbao", "pedro@example.com", "2023-11-12"],
        [7, "Sofía Torres", "Madrid", "sofia@example.com", "2024-02-28"],
        [8, "Diego Ramírez", "Valencia", "diego@example.com", "2024-06-15"]
      ]),
    productos: makeTable(
      [["id", "INTEGER", PK], ["nombre", "TEXT", NN], ["categoria", "TEXT"], ["precio", "REAL"], ["stock", "INTEGER"]],
      [
        [1, "Laptop Pro 14", "Electrónica", 1299.99, 25],
        [2, "Mouse Inalámbrico", "Accesorios", 19.99, 150],
        [3, "Teclado Mecánico", "Accesorios", 89.5, 60],
        [4, 'Monitor 27"', "Electrónica", 249.0, 40],
        [5, "Disco SSD 1TB", "Componentes", 109.9, 80],
        [6, "Memoria RAM 16GB", "Componentes", 65.5, 95],
        [7, "Webcam HD", "Accesorios", 45.0, 70],
        [8, "Auriculares BT", "Audio", 59.99, 120],
        [9, "Altavoz Portátil", "Audio", 39.95, 90],
        [10, "Hub USB-C", "Accesorios", 29.99, 110]
      ]),
    pedidos: makeTable(
      [["id", "INTEGER", PK], ["cliente_id", "INTEGER", NN], ["fecha", "TEXT"], ["estado", "TEXT"]],
      [
        [1, 1, "2024-01-10", "entregado"], [2, 2, "2024-01-15", "entregado"],
        [3, 1, "2024-02-03", "entregado"], [4, 3, "2024-02-20", "enviado"],
        [5, 5, "2024-03-01", "entregado"], [6, 4, "2024-03-15", "pendiente"],
        [7, 2, "2024-04-02", "enviado"], [8, 7, "2024-04-18", "entregado"],
        [9, 3, "2024-05-05", "pendiente"], [10, 8, "2024-05-21", "enviado"],
        [11, 1, "2024-06-10", "entregado"], [12, 6, "2024-06-25", "pendiente"]
      ]),
    detalle_pedidos: makeTable(
      [["pedido_id", "INTEGER", NN], ["producto_id", "INTEGER", NN], ["cantidad", "INTEGER"], ["precio_unitario", "REAL"]],
      [
        [1, 1, 1, 1299.99], [1, 2, 2, 19.99], [2, 4, 1, 249.0], [2, 3, 1, 89.5],
        [3, 5, 2, 109.9], [3, 8, 1, 59.99], [4, 2, 1, 19.99], [4, 9, 2, 39.95],
        [5, 1, 1, 1299.99], [5, 7, 1, 45.0], [6, 6, 2, 65.5], [7, 10, 3, 29.99],
        [7, 2, 1, 19.99], [8, 4, 2, 249.0], [9, 8, 2, 59.99], [10, 3, 1, 89.5],
        [10, 5, 1, 109.9], [11, 9, 1, 39.95], [12, 1, 1, 1299.99], [12, 6, 1, 65.5]
      ])
  };
}

function seedEmpleados() {
  return {
    departamentos: makeTable(
      [["id", "INTEGER", PK], ["nombre", "TEXT", NN], ["ubicacion", "TEXT"]],
      [
        [1, "Ingeniería", "Madrid"], [2, "Ventas", "Barcelona"],
        [3, "Recursos Humanos", "Madrid"], [4, "Finanzas", "Valencia"]
      ]),
    empleados: makeTable(
      [["id", "INTEGER", PK], ["nombre", "TEXT", NN], ["puesto", "TEXT"], ["departamento_id", "INTEGER"], ["salario", "REAL"], ["fecha_contratacion", "TEXT"]],
      [
        [1, "Ana Pérez", "Desarrolladora Sr", 1, 52000, "2019-03-01"],
        [2, "Luis Gómez", "Desarrollador", 1, 38000, "2021-06-15"],
        [3, "Marta Díaz", "Team Lead", 1, 61000, "2017-09-10"],
        [4, "Jorge Silva", "Comercial", 2, 32000, "2020-01-20"],
        [5, "Paula Ríos", "Comercial Sr", 2, 41000, "2018-11-05"],
        [6, "Andrés Cano", "Analista RRHH", 3, 30000, "2022-02-14"],
        [7, "Lucía Vega", "Contable", 4, 35000, "2019-08-30"],
        [8, "Hugo Marín", "Director Financiero", 4, 70000, "2015-04-01"],
        [9, "Elena Ortiz", "Desarrolladora", 1, 36000, "2023-01-09"],
        [10, "Marcos Gil", "Comercial", 2, 29000, "2023-07-19"]
      ]),
    proyectos: makeTable(
      [["id", "INTEGER", PK], ["nombre", "TEXT", NN], ["presupuesto", "REAL"]],
      [
        [1, "Nueva Web", 120000], [2, "App Móvil", 200000],
        [3, "CRM Ventas", 90000], [4, "Auditoría 2024", 40000]
      ]),
    asignaciones: makeTable(
      [["empleado_id", "INTEGER", NN], ["proyecto_id", "INTEGER", NN], ["horas", "INTEGER"]],
      [
        [1, 1, 480], [2, 1, 720], [3, 2, 300], [9, 2, 650], [4, 3, 200],
        [5, 3, 410], [10, 3, 150], [7, 4, 260], [8, 4, 90]
      ])
  };
}

function seedBiblioteca() {
  return {
    autores: makeTable(
      [["id", "INTEGER", PK], ["nombre", "TEXT", NN], ["nacionalidad", "TEXT"]],
      [
        [1, "Gabriel García Márquez", "Colombia"], [2, "Isabel Allende", "Chile"],
        [3, "Mario Vargas Llosa", "Perú"], [4, "Jorge Luis Borges", "Argentina"],
        [5, "Almudena Grandes", "España"]
      ]),
    libros: makeTable(
      [["id", "INTEGER", PK], ["titulo", "TEXT", NN], ["autor_id", "INTEGER"], ["anio", "INTEGER"], ["genero", "TEXT"], ["copias", "INTEGER"]],
      [
        [1, "Cien años de soledad", 1, 1967, "Novela", 5],
        [2, "El amor en los tiempos del cólera", 1, 1985, "Novela", 3],
        [3, "La casa de los espíritus", 2, 1982, "Novela", 4],
        [4, "La ciudad y los perros", 3, 1963, "Novela", 2],
        [5, "Ficciones", 4, 1944, "Cuentos", 3],
        [6, "El Aleph", 4, 1949, "Cuentos", 2],
        [7, "Corazón helado", 5, 2007, "Novela", 3],
        [8, "Los pacientes del doctor García", 5, 2017, "Novela", 2]
      ]),
    socios: makeTable(
      [["id", "INTEGER", PK], ["nombre", "TEXT", NN], ["email", "TEXT"], ["fecha_alta", "TEXT"]],
      [
        [1, "Marta Ceballos", "marta@example.com", "2021-03-10"],
        [2, "Iván Ortega", "ivan@example.com", "2021-09-01"],
        [3, "Sara Molina", "sara@example.com", "2022-01-15"],
        [4, "Raúl Iglesias", "raul@example.com", "2023-06-20"],
        [5, "Paula Neira", "paula@example.com", "2024-02-05"]
      ]),
    prestamos: makeTable(
      [["id", "INTEGER", PK], ["libro_id", "INTEGER", NN], ["socio_id", "INTEGER", NN], ["fecha_prestamo", "TEXT"], ["fecha_devolucion", "TEXT"]],
      [
        [1, 1, 1, "2024-09-01", "2024-09-15"],
        [2, 3, 2, "2024-09-10", "2024-09-25"],
        [3, 5, 1, "2024-10-02", null],
        [4, 2, 3, "2024-10-05", null],
        [5, 6, 4, "2024-10-12", "2024-10-26"],
        [6, 1, 5, "2024-11-01", null],
        [7, 7, 2, "2024-11-03", "2024-11-20"],
        [8, 4, 3, "2024-11-10", null],
        [9, 8, 4, "2024-11-15", "2024-12-01"],
        [10, 5, 5, "2024-12-01", null]
      ])
  };
}

const DB_SEEDS = { tienda: seedTienda, empleados: seedEmpleados, biblioteca: seedBiblioteca };
const DB_KEYS = ["tienda", "empleados", "biblioteca"];
const DB_INFO = {
  tienda: { label: "Tienda", emoji: "\u{1F6D2}", desc: "Clientes, productos, pedidos y líneas de pedido." },
  empleados: { label: "Empleados", emoji: "\u{1F465}", desc: "Departamentos, empleados, proyectos y asignaciones." },
  biblioteca: { label: "Biblioteca", emoji: "\u{1F4DA}", desc: "Autores, libros, socios y préstamos." }
};

/** Devuelve una copia fresca (seed) de una base de datos de ejemplo. */
function freshDb(key) {
  if (!DB_SEEDS[key]) throw new SqlError('Base de datos desconocida: "' + key + '".', "Bases disponibles: " + DB_KEYS.join(", ") + ".");
  return { name: key, tables: DB_SEEDS[key]() };
}

/* ============================= Resaltado de sintaxis ============================= */

function esc(s) {
  return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
}

/** Resalta SQL a HTML seguro (usa el mismo tokenizer que el motor: WYSIWYG). */
function highlightSql(sql) {
  let tokens;
  try { tokens = tokenize(sql); }
  catch (e) { return esc(sql); }
  let out = "";
  let last = 0;
  for (const tk of tokens) {
    if (tk.type === "eof") break;
    out += esc(sql.slice(last, tk.pos));
    const text = esc(sql.slice(tk.pos, tk.end));
    if (tk.type === "kw") out += '<span class="tk-kw">' + text + "</span>";
    else if (tk.type === "string") out += '<span class="tk-str">' + text + "</span>";
    else if (tk.type === "number") out += '<span class="tk-num">' + text + "</span>";
    else if (tk.type === "comment") out += '<span class="tk-com">' + text + "</span>";
    else if (tk.type === "ident") {
      if (SQL_FUNCTIONS.has(String(tk.value).toUpperCase())) out += '<span class="tk-fn">' + text + "</span>";
      else out += text;
    } else out += text;
    last = tk.end;
  }
  out += esc(sql.slice(last));
  return out;
}
/* ===== SQLAB ENGINE END ===== */

/* ===== HELPERS DE VALIDACIÓN (tests de lecciones y desafíos) ===== */
function lastRowsRes(out) {
  const rs = (out && out.results ? out.results : []).filter((x) => x.kind === "rows");
  return rs.length ? rs[rs.length - 1] : null;
}
function lastRows(out) { const r = lastRowsRes(out); return r ? r.rows : null; }
function near(a, b, eps) { return typeof a === "number" && Math.abs(a - b) <= (eps === undefined ? 0.011 : eps); }
function tbl(db, name) { return db.tables[name]; }

/* ===== SUITE DE TESTS (se ejecuta en la vista "Tests"; espejo de los tests de CI) ===== */
function runTestSuite() {
  const results = [];
  const t00 = Date.now();
  const test = (group, name, fn) => {
    const t0 = Date.now();
    try { fn(); results.push({ group, name, status: "pass", ms: Math.round((Date.now() - t0) * 10) / 10 }); }
    catch (e) { results.push({ group, name, status: "fail", ms: Math.round((Date.now() - t0) * 10) / 10, error: (e && e.message) || String(e) }); }
  };
  const assert = (cond, msg) => { if (!cond) throw new Error(msg || "Comprobación fallida"); };
  const eq = (a, b, msg) => {
    const ja = JSON.stringify(a); const jb = JSON.stringify(b);
    if (ja !== jb) throw new Error((msg ? msg + " — " : "") + "esperado " + jb + ", obtenido " + ja);
  };
  const run = (dbKey, sql) => { const db = freshDb(dbKey); const out = executeScript(db, sql); return { db, out }; };
  const okRun = (dbKey, sql) => {
    const r = run(dbKey, sql);
    if (!r.out.ok) throw new Error("Error inesperado: " + r.out.error.message);
    return r;
  };
  const badRun = (dbKey, sql, includes) => {
    const r = run(dbKey, sql);
    assert(!r.out.ok, "La consulta debería haber fallado: " + sql);
    if (includes) {
      const hay = String(r.out.error.message) + " " + String(r.out.error.hint || "");
      assert(hay.toLowerCase().indexOf(includes.toLowerCase()) !== -1,
        'El error debería incluir "' + includes + '". Obtenido: ' + r.out.error.message);
    }
    return r;
  };
  const rows0 = (out) => { const rs = out.results.filter((x) => x.kind === "rows"); return rs.length ? rs[0].rows : null; };

  /* ---------- Seguridad y validación ---------- */
  const G1 = "Seguridad y validación";
  test(G1, "Rechaza scripts vacíos", () => { badRun("tienda", "   ", "vacío"); });
  test(G1, "Rechaza scripts que solo contienen comentarios", () => { badRun("tienda", "-- nada\n/* nada */", "vacío"); });
  test(G1, "Bloquea PRAGMA (introspección del SGBD)", () => { badRun("tienda", "PRAGMA table_info(clientes);", "no está permitida"); });
  test(G1, "Bloquea ATTACH DATABASE", () => { badRun("tienda", 'ATTACH DATABASE "x" AS y;', "no está permitida"); });
  test(G1, "Bloquea ALTER TABLE", () => { badRun("tienda", "ALTER TABLE clientes ADD COLUMN t TEXT;", "no está permitida"); });
  test(G1, "Bloquea sentencias fuera de la lista blanca (TRUNCATE)", () => { badRun("tienda", "TRUNCATE TABLE clientes;", "no permitida"); });
  test(G1, "Una literal con SQL dentro se trata como DATO (anti-inyección)", () => {
    const r = okRun("tienda", "SELECT * FROM clientes WHERE nombre = 'x''; DROP TABLE clientes; --';");
    eq(rows0(r.out).length, 0, "0 filas");
    assert(hasOwn(r.db.tables, "clientes"), "la tabla clientes sigue existiendo");
    eq(r.db.tables.clientes.rows.length, 8);
  });
  test(G1, "Rechaza scripts que superan la longitud máxima", () => {
    badRun("tienda", "SELECT " + "1 + ".repeat(6000) + "1", "máximo");
  });
  test(G1, "Rechaza más sentencias de las permitidas", () => {
    badRun("tienda", new Array(30).fill("SELECT 1").join("; ") + ";", "Demasiadas");
  });
  test(G1, "Permite varias sentencias seguras separadas por ';'", () => {
    const r = okRun("tienda", "SELECT 1; SELECT 2; SELECT 3;");
    eq(r.out.results.length, 3);
  });
  test(G1, "Los comentarios no rompen la ejecución", () => {
    const r = okRun("tienda", "SELECT COUNT(*) FROM clientes; -- comentario\n/* otro */");
    eq(rows0(r.out)[0][0], 8);
  });

  /* ---------- SELECT y filtrado ---------- */
  const G2 = "SELECT y filtrado";
  test(G2, "SELECT * devuelve todas las filas y columnas", () => {
    const r = okRun("tienda", "SELECT * FROM clientes;");
    const res = r.out.results[0];
    eq(res.rowCount, 8);
    eq(res.columns, ["id", "nombre", "ciudad", "email", "fecha_registro"]);
    eq(res.rows[0], [1, "Ana García", "Madrid", "ana@example.com", "2022-01-15"]);
  });
  test(G2, "La proyección respeta el orden pedido", () => {
    const r = okRun("tienda", "SELECT ciudad, nombre FROM clientes WHERE id = 1;");
    eq(r.out.results[0].columns, ["ciudad", "nombre"]);
    eq(rows0(r.out), [["Madrid", "Ana García"]]);
  });
  test(G2, "WHERE con AND/OR y paréntesis", () => {
    const r = okRun("tienda", "SELECT COUNT(*) FROM productos WHERE (categoria = 'Audio' OR categoria = 'Accesorios') AND precio < 50;");
    eq(rows0(r.out)[0][0], 4);
  });
  test(G2, "LIKE con % y _", () => {
    eq(rows0(okRun("tienda", "SELECT COUNT(*) FROM clientes WHERE nombre LIKE 'A%';").out)[0][0], 1);
    eq(rows0(okRun("tienda", "SELECT COUNT(*) FROM clientes WHERE nombre LIKE '_na%';").out)[0][0], 1);
  });
  test(G2, "IN y NOT IN con listas", () => {
    const r = okRun("tienda", "SELECT nombre FROM productos WHERE id IN (1, 4, 7) ORDER BY id;");
    eq(rows0(r.out), [["Laptop Pro 14"], ['Monitor 27"'], ["Webcam HD"]]);
    eq(rows0(okRun("tienda", "SELECT COUNT(*) FROM productos WHERE id NOT IN (1, 2);").out)[0][0], 8);
  });
  test(G2, "BETWEEN es inclusivo", () => {
    eq(rows0(okRun("tienda", "SELECT COUNT(*) FROM productos WHERE precio BETWEEN 40 AND 90;").out)[0][0], 4);
  });
  test(G2, "IS NULL / IS NOT NULL", () => {
    eq(rows0(okRun("biblioteca", "SELECT COUNT(*) FROM prestamos WHERE fecha_devolucion IS NULL;").out)[0][0], 5);
    eq(rows0(okRun("biblioteca", "SELECT COUNT(*) FROM prestamos WHERE fecha_devolucion IS NOT NULL;").out)[0][0], 5);
  });
  test(G2, "DISTINCT elimina duplicados", () => {
    eq(rows0(okRun("tienda", "SELECT DISTINCT ciudad FROM clientes;").out).length, 5);
  });
  test(G2, "ORDER BY DESC + LIMIT + OFFSET", () => {
    const r = okRun("tienda", "SELECT nombre FROM productos ORDER BY precio DESC LIMIT 2 OFFSET 1;");
    eq(rows0(r.out), [['Monitor 27"'], ["Disco SSD 1TB"]]);
  });
  test(G2, "ORDER BY por alias y por posición", () => {
    eq(rows0(okRun("tienda", "SELECT precio AS p FROM productos ORDER BY p DESC LIMIT 1;").out), [[1299.99]]);
    eq(rows0(okRun("tienda", "SELECT nombre, precio FROM productos ORDER BY 2 ASC LIMIT 1;").out), [["Mouse Inalámbrico", 19.99]]);
  });
  test(G2, "Comparaciones numéricas", () => {
    eq(rows0(okRun("empleados", "SELECT COUNT(*) FROM empleados WHERE salario > 40000;").out)[0][0], 4);
  });
  test(G2, "Funciones escalares (UPPER, LENGTH, ROUND)", () => {
    eq(rows0(okRun("tienda", "SELECT UPPER(nombre), LENGTH(nombre), ROUND(precio * 1.1, 2) FROM productos WHERE id = 8;").out),
      [["AURICULARES BT", 14, 65.99]]);
  });
  test(G2, "COALESCE y SUBSTR", () => {
    eq(rows0(okRun("biblioteca", "SELECT COALESCE(fecha_devolucion, 'activo') FROM prestamos WHERE id = 3;").out), [["activo"]]);
    eq(rows0(okRun("tienda", "SELECT SUBSTR('SQLab', 2, 3);").out), [["QLa"]]);
  });
  test(G2, "CASE WHEN clasifica valores", () => {
    eq(rows0(okRun("tienda", "SELECT COUNT(*) FROM productos WHERE CASE WHEN precio > 500 THEN 1 ELSE 0 END = 1;").out)[0][0], 1);
  });
  test(G2, "Aritmética, división por cero (NULL) y concatenación ||", () => {
    eq(rows0(okRun("tienda", "SELECT 7 / 2, 1 / 0, 7 % 2;").out), [[3.5, null, 1]]);
    eq(rows0(okRun("tienda", "SELECT 'a' || 'b';").out), [["ab"]]);
  });
  test(G2, "Lógica booleana con NOT", () => {
    eq(rows0(okRun("tienda", "SELECT COUNT(*) FROM clientes WHERE ciudad = 'Madrid' AND NOT nombre LIKE 'A%';").out)[0][0], 2);
  });

  /* ---------- Agregación y GROUP BY ---------- */
  const G3 = "Agregación y GROUP BY";
  test(G3, "COUNT(*) global", () => { eq(rows0(okRun("tienda", "SELECT COUNT(*) FROM pedidos;").out)[0][0], 12); });
  test(G3, "COUNT(*) sobre conjunto vacío devuelve 0", () => {
    eq(rows0(okRun("tienda", "SELECT COUNT(*) FROM clientes WHERE 1 = 0;").out), [[0]]);
  });
  test(G3, "SUM exacto por grupo", () => {
    const v = rows0(okRun("tienda", "SELECT SUM(cantidad * precio_unitario) FROM detalle_pedidos WHERE pedido_id = 1;").out)[0][0];
    assert(near(v, 1339.97), "SUM pedido 1 ~= 1339.97, obtenido " + v);
  });
  test(G3, "AVG con ROUND", () => {
    const v = rows0(okRun("tienda", "SELECT ROUND(AVG(precio), 2) FROM productos;").out)[0][0];
    assert(near(v, 200.88), "AVG ~= 200.88, obtenido " + v);
  });
  test(G3, "GROUP BY + COUNT + ORDER BY", () => {
    eq(rows0(okRun("tienda", "SELECT cliente_id, COUNT(*) AS c FROM pedidos GROUP BY cliente_id ORDER BY c DESC, cliente_id LIMIT 1;").out), [[1, 3]]);
  });
  test(G3, "HAVING filtra grupos", () => {
    eq(rows0(okRun("tienda", "SELECT cliente_id FROM pedidos GROUP BY cliente_id HAVING COUNT(*) >= 2 ORDER BY cliente_id;").out), [[1], [2], [3]]);
  });
  test(G3, "MIN/MAX sobre texto y número", () => {
    eq(rows0(okRun("tienda", "SELECT MIN(nombre), MAX(precio) FROM productos;").out), [["Altavoz Portátil", 1299.99]]);
  });
  test(G3, "COUNT(DISTINCT col)", () => {
    eq(rows0(okRun("tienda", "SELECT COUNT(DISTINCT ciudad) FROM clientes;").out)[0][0], 5);
  });
  test(G3, "SUM ignora NULL y COUNT(*) cuenta filas", () => {
    const r = okRun("tienda", "CREATE TABLE t (a REAL); INSERT INTO t VALUES (1), (NULL), (2); SELECT SUM(a), COUNT(a), COUNT(*) FROM t;");
    eq(rows0(r.out), [[3, 2, 3]]);
  });
  test(G3, "GROUP BY por dos columnas", () => {
    const r = okRun("tienda", "SELECT categoria, COUNT(*) FROM productos GROUP BY categoria ORDER BY categoria;");
    eq(rows0(r.out), [["Accesorios", 4], ["Audio", 2], ["Componentes", 2], ["Electrónica", 2]]);
  });

  /* ---------- JOINs ---------- */
  const G4 = "JOINs";
  test(G4, "INNER JOIN combina filas relacionadas", () => {
    eq(rows0(okRun("tienda", "SELECT COUNT(*) FROM pedidos p JOIN clientes c ON c.id = p.cliente_id;").out)[0][0], 12);
  });
  test(G4, "LEFT JOIN conserva filas sin coincidencia", () => {
    eq(rows0(okRun("empleados", "SELECT COUNT(*) FROM empleados e LEFT JOIN asignaciones a ON a.empleado_id = e.id;").out)[0][0], 10);
    eq(rows0(okRun("empleados", "SELECT COUNT(*) FROM empleados e JOIN asignaciones a ON a.empleado_id = e.id;").out)[0][0], 9);
  });
  test(G4, "RIGHT JOIN", () => {
    eq(rows0(okRun("empleados", "SELECT COUNT(*) FROM asignaciones a RIGHT JOIN empleados e ON a.empleado_id = e.id;").out)[0][0], 10);
  });
  test(G4, "JOIN de 3 tablas", () => {
    eq(rows0(okRun("biblioteca", "SELECT COUNT(*) FROM prestamos p JOIN libros l ON l.id = p.libro_id JOIN socios s ON s.id = p.socio_id;").out)[0][0], 10);
  });
  test(G4, "Producto cartesiano con coma", () => {
    eq(rows0(okRun("empleados", "SELECT COUNT(*) FROM departamentos, proyectos;").out)[0][0], 16);
  });
  test(G4, "Columnas cualificadas con alias", () => {
    eq(rows0(okRun("tienda", "SELECT c.nombre, p.fecha FROM pedidos p JOIN clientes c ON c.id = p.cliente_id WHERE p.id = 1;").out),
      [["Ana García", "2024-01-10"]]);
  });
  test(G4, "Columna ambigua produce error didáctico", () => {
    badRun("tienda", "SELECT id FROM pedidos JOIN clientes ON cliente_id = clientes.id;", "ambigua");
  });
  test(G4, "Alias repetido en FROM produce error", () => {
    badRun("tienda", "SELECT * FROM pedidos p JOIN clientes p ON p.id = p.id;", "más de una vez");
  });
  test(G4, "Subconsulta en FROM exige alias", () => {
    badRun("tienda", "SELECT * FROM (SELECT 1 AS x);", "alias");
  });
  test(G4, "JOIN + agregado + HAVING", () => {
    eq(rows0(okRun("tienda", "SELECT c.nombre, COUNT(p.id) FROM clientes c LEFT JOIN pedidos p ON p.cliente_id = c.id GROUP BY c.nombre HAVING COUNT(p.id) = 3;").out),
      [["Ana García", 3]]);
  });

  /* ---------- Subconsultas, CTE y conjuntos ---------- */
  const G5 = "Subconsultas, CTE y conjuntos";
  test(G5, "Subconsulta escalar en WHERE", () => {
    eq(rows0(okRun("tienda", "SELECT COUNT(*) FROM productos WHERE precio > (SELECT AVG(precio) FROM productos);").out)[0][0], 2);
  });
  test(G5, "IN con subconsulta", () => {
    eq(rows0(okRun("tienda", "SELECT COUNT(*) FROM clientes WHERE id IN (SELECT cliente_id FROM pedidos WHERE estado = 'pendiente');").out)[0][0], 3);
  });
  test(G5, "EXISTS no correlacionado", () => {
    eq(rows0(okRun("tienda", "SELECT COUNT(*) FROM clientes WHERE EXISTS (SELECT 1 FROM pedidos WHERE estado = 'pendiente');").out)[0][0], 8);
  });
  test(G5, "Subconsulta escalar con varias filas da error claro", () => {
    badRun("tienda", "SELECT (SELECT precio FROM productos) FROM clientes;", "La subconsulta");
  });
  test(G5, "UNION deduplica y UNION ALL no", () => {
    eq(rows0(okRun("empleados", "SELECT ubicacion FROM departamentos UNION SELECT ubicacion FROM departamentos;").out).length, 3);
    eq(rows0(okRun("empleados", "SELECT ubicacion FROM departamentos UNION ALL SELECT ubicacion FROM departamentos;").out).length, 6);
  });
  test(G5, "INTERSECT y EXCEPT", () => {
    eq(rows0(okRun("tienda", "SELECT ciudad FROM clientes INTERSECT SELECT 'Madrid';").out), [["Madrid"]]);
    eq(rows0(okRun("tienda", "SELECT categoria FROM productos EXCEPT SELECT 'Audio';").out).length, 3);
  });
  test(G5, "CTE (WITH) materializa resultados", () => {
    const r = okRun("tienda", "WITH ingresos AS (SELECT pedido_id, SUM(cantidad * precio_unitario) AS total FROM detalle_pedidos GROUP BY pedido_id) SELECT pedido_id, ROUND(total, 2) AS total FROM ingresos WHERE total > 200 ORDER BY total DESC;");
    const rows = rows0(r.out);
    eq(rows.length, 6);
    eq(rows[0][0], 12);
    assert(near(rows[0][1], 1365.49), "total pedido 12 ~= 1365.49");
  });
  test(G5, "CTE encadenadas", () => {
    eq(rows0(okRun("tienda", "WITH a AS (SELECT 1 AS x), b AS (SELECT x + 1 AS y FROM a) SELECT y FROM b;").out), [[2]]);
  });
  test(G5, "Tabla derivada en FROM con JOIN", () => {
    const r = okRun("empleados", "SELECT e.nombre FROM empleados e JOIN (SELECT departamento_id, AVG(salario) AS media FROM empleados GROUP BY departamento_id) d ON e.departamento_id = d.departamento_id WHERE e.salario > d.media ORDER BY e.nombre;");
    eq(rows0(r.out), [["Ana Pérez"], ["Hugo Marín"], ["Marta Díaz"], ["Paula Ríos"]]);
  });
  test(G5, "CTE + agregado posterior", () => {
    eq(rows0(okRun("tienda", "WITH t AS (SELECT cliente_id, COUNT(*) AS n FROM pedidos GROUP BY cliente_id) SELECT COUNT(*) FROM t WHERE n > 1;").out)[0][0], 3);
  });

  /* ---------- DML y DDL ---------- */
  const G6 = "DML y DDL";
  test(G6, "INSERT añade fila con NULL en columnas omitidas", () => {
    const r = okRun("tienda", "INSERT INTO clientes (id, nombre, ciudad) VALUES (9, 'Elena', 'Zaragoza'); SELECT COUNT(*) FROM clientes;");
    eq(rows0(r.out)[0][0], 9);
    eq(r.db.tables.clientes.rows[8].email, null);
  });
  test(G6, "INSERT con VALUES múltiple", () => {
    eq(rows0(okRun("tienda", "INSERT INTO clientes (id, nombre) VALUES (9, 'A'), (10, 'B'); SELECT COUNT(*) FROM clientes;").out)[0][0], 10);
  });
  test(G6, "INSERT viola NOT NULL -> error", () => {
    badRun("tienda", "INSERT INTO clientes (id, ciudad) VALUES (10, 'X');", "NULL");
  });
  test(G6, "INSERT con PRIMARY KEY duplicada -> error", () => {
    badRun("tienda", "INSERT INTO clientes (id, nombre) VALUES (1, 'X');", "ya existe");
  });
  test(G6, "INSERT con nº de valores incorrecto -> error", () => {
    badRun("tienda", "INSERT INTO clientes (id, nombre) VALUES (9);", "valores");
  });
  test(G6, "UPDATE modifica solo las filas filtradas", () => {
    const r = okRun("tienda", "UPDATE productos SET stock = 0 WHERE categoria = 'Audio'; SELECT COUNT(*) FROM productos WHERE stock = 0;");
    eq(rows0(r.out)[0][0], 2);
    eq(r.db.tables.productos.rows[0].stock, 25);
  });
  test(G6, "UPDATE sin WHERE emite aviso", () => {
    const r = okRun("tienda", "UPDATE productos SET stock = 1;");
    assert(r.out.messages.some((m) => m.type === "warning" && m.text.indexOf("WHERE") !== -1), "debe avisar del UPDATE sin WHERE");
  });
  test(G6, "UPDATE con aritmética sobre la propia columna", () => {
    const v = rows0(okRun("empleados", "UPDATE empleados SET salario = salario * 1.1 WHERE id = 1; SELECT salario FROM empleados WHERE id = 1;").out)[0][0];
    assert(near(v, 57200, 1), "salario ~= 57200, obtenido " + v);
  });
  test(G6, "DELETE elimina según WHERE", () => {
    eq(rows0(okRun("biblioteca", "DELETE FROM prestamos WHERE fecha_devolucion IS NOT NULL; SELECT COUNT(*) FROM prestamos;").out)[0][0], 5);
  });
  test(G6, "DELETE sin WHERE emite aviso", () => {
    const r = okRun("tienda", "DELETE FROM clientes;");
    assert(r.out.messages.some((m) => m.type === "warning"), "debe avisar");
  });
  test(G6, "CREATE TABLE + INSERT + SELECT + DROP TABLE", () => {
    const r = run("tienda", "CREATE TABLE tmp (x INTEGER); INSERT INTO tmp VALUES (5); SELECT x FROM tmp;");
    assert(r.out.ok, "script válido: " + (r.out.error ? r.out.error.message : ""));
    eq(rows0(r.out), [[5]]);
    const r2 = executeScript(r.db, "DROP TABLE tmp; SELECT * FROM tmp;");
    assert(!r2.ok && r2.error.message.indexOf("No existe la tabla") !== -1, "tras DROP la tabla no existe");
  });
  test(G6, "CREATE TABLE sobre tabla existente falla; IF NOT EXISTS no", () => {
    badRun("tienda", "CREATE TABLE clientes (a TEXT);", "ya existe");
    okRun("tienda", "CREATE TABLE IF NOT EXISTS clientes (a TEXT);");
  });
  test(G6, "CREATE TABLE ... AS SELECT", () => {
    eq(rows0(okRun("tienda", "CREATE TABLE caras AS SELECT nombre, precio FROM productos WHERE precio > 500; SELECT COUNT(*) FROM caras;").out)[0][0], 1);
  });
  test(G6, "INSERT ... SELECT", () => {
    const sql = "CREATE TABLE copia AS SELECT * FROM clientes WHERE 1 = 0; INSERT INTO copia (id, nombre, ciudad, email, fecha_registro) SELECT id, nombre, ciudad, email, fecha_registro FROM clientes; SELECT COUNT(*) FROM copia;";
    eq(rows0(okRun("tienda", sql).out)[0][0], 8);
  });
  test(G6, "INTEGER PRIMARY KEY AUTOINCREMENT genera ids", () => {
    const r = okRun("tienda", "CREATE TABLE notas (id INTEGER PRIMARY KEY AUTOINCREMENT, texto TEXT); INSERT INTO notas (texto) VALUES ('a'), ('b'); SELECT id, texto FROM notas;");
    eq(rows0(r.out), [[1, "a"], [2, "b"]]);
  });

  /* ---------- Transacciones ---------- */
  const G7 = "Transacciones";
  test(G7, "BEGIN + ROLLBACK deshace cambios", () => {
    eq(rows0(okRun("tienda", "BEGIN; DELETE FROM clientes; ROLLBACK; SELECT COUNT(*) FROM clientes;").out)[0][0], 8);
  });
  test(G7, "BEGIN + COMMIT conserva cambios", () => {
    eq(rows0(okRun("tienda", "BEGIN; DELETE FROM clientes; COMMIT; SELECT COUNT(*) FROM clientes;").out)[0][0], 0);
  });
  test(G7, "ROLLBACK sin BEGIN -> error claro", () => { badRun("tienda", "ROLLBACK;", "transacción"); });
  test(G7, "BEGIN doble -> error claro", () => { badRun("tienda", "BEGIN; BEGIN;", "transacción"); });
  test(G7, "ROLLBACK revierte UPDATE", () => {
    eq(rows0(okRun("tienda", "BEGIN; UPDATE productos SET precio = 0; ROLLBACK; SELECT precio FROM productos WHERE id = 1;").out)[0][0], 1299.99);
  });

  /* ---------- Manejo de errores ---------- */
  const G8 = "Manejo de errores";
  test(G8, "Tabla inexistente: mensaje + pista con alternativas", () => {
    const r = badRun("tienda", "SELECT * FROM usuarios;", "No existe la tabla");
    assert(String(r.out.error.hint).indexOf("productos") !== -1, "la pista lista las tablas disponibles");
  });
  test(G8, "Columna inexistente: mensaje + columnas disponibles", () => {
    const r = badRun("tienda", "SELECT telefono FROM clientes;", "No existe la columna");
    assert(String(r.out.error.hint).indexOf("nombre") !== -1, "la pista lista columnas");
  });
  test(G8, "Error de sintaxis indica posición", () => {
    badRun("tienda", "SELECT * FROM clientes WHERE;", "sintaxis");
  });
  test(G8, "Palabra clave mal escrita se rechaza", () => {
    badRun("tienda", "SELCT * FROM clientes;", "no permitida");
  });
  test(G8, "Texto sin cerrar", () => {
    badRun("tienda", "SELECT * FROM clientes WHERE ciudad = 'Madrid", "sin cerrar");
  });
  test(G8, "Agregado dentro de WHERE sugiere HAVING", () => {
    badRun("tienda", "SELECT COUNT(*) FROM clientes WHERE COUNT(*) > 1;", "HAVING");
  });
  test(G8, "Función desconocida sugiere las disponibles", () => {
    const r = badRun("tienda", "SELECT FOO(1);", "Función desconocida");
    assert(String(r.out.error.hint).indexOf("COUNT") !== -1, "la pista lista funciones");
  });
  test(G8, "executeScript NUNCA lanza (contrato de robustez)", () => {
    const out = executeScript(freshDb("tienda"), "(((( ;");
    assert(out.ok === false && typeof out.error.message === "string", "error serializado");
  });
  test(G8, "freshDb con clave inválida lanza SqlError", () => {
    let lanzo = false;
    try { freshDb("inexistente"); } catch (e) { lanzo = e instanceof SqlError; }
    assert(lanzo, "debe lanzar SqlError");
  });

  /* ---------- Contrato y experiencia de usuario ---------- */
  const G9 = "Contrato y experiencia de usuario";
  test(G9, "executeScript devuelve el contrato {ok, results, messages, error, ms}", () => {
    const out = executeScript(freshDb("tienda"), "SELECT 1;");
    assert(typeof out.ok === "boolean" && Array.isArray(out.results) && Array.isArray(out.messages) && typeof out.ms === "number", "contrato");
    assert(out.error === null, "sin error");
  });
  test(G9, "Cada fila tiene la misma longitud que columns", () => {
    const r = okRun("tienda", "SELECT * FROM pedidos p JOIN clientes c ON c.id = p.cliente_id;");
    const res = r.out.results[0];
    eq(res.columns.length, 9);
    res.rows.forEach((row) => eq(row.length, res.columns.length));
  });
  test(G9, "LIMIT limita rowCount", () => {
    eq(okRun("tienda", "SELECT * FROM productos LIMIT 3;").out.results[0].rowCount, 3);
  });
  test(G9, "freshDb restaura el seed tras mutaciones destructivas", () => {
    const db1 = freshDb("tienda");
    executeScript(db1, "DELETE FROM clientes; DROP TABLE productos;");
    const db2 = freshDb("tienda");
    eq(db2.tables.clientes.rows.length, 8);
    assert(hasOwn(db2.tables, "productos"), "productos restaurado");
  });
  test(G9, "highlightSql escapa HTML (anti-XSS en el editor)", () => {
    const h = highlightSql("SELECT '<b>'");
    assert(h.indexOf("&lt;b&gt;") !== -1 && h.indexOf("<b>") === -1, "HTML escapado");
  });
  test(G9, "highlightSql marca palabras clave", () => {
    assert(highlightSql("SELECT 1").indexOf("tk-kw") !== -1, "clase tk-kw presente");
  });
  test(G9, "highlightSql no lanza con SQL inválido (degradación elegante)", () => {
    const h = highlightSql("SELECT 'sin cerrar");
    assert(typeof h === "string" && h.length > 0, "devuelve texto escapado");
  });
  test(G9, "Las 3 bases de ejemplo arrancan con sus tablas", () => {
    eq(Object.keys(freshDb("tienda").tables).sort(), ["clientes", "detalle_pedidos", "pedidos", "productos"]);
    eq(Object.keys(freshDb("empleados").tables).sort(), ["asignaciones", "departamentos", "empleados", "proyectos"]);
    eq(Object.keys(freshDb("biblioteca").tables).sort(), ["autores", "libros", "prestamos", "socios"]);
  });

  const passed = results.filter((r) => r.status === "pass").length;
  return { results, total: results.length, passed, failed: results.length - passed, ms: Date.now() - t00 };
}
/* ===== SUITE DE TESTS END ===== */

/* ============================================================================
 * CONTENIDO EDUCATIVO
 * ========================================================================== */

const LEVELS = ["Básico", "Intermedio", "Avanzado"];

const LESSONS = [
  {
    id: "basico-1", level: "Básico", title: "¿Qué es SQL? Tu primer SELECT", minutes: 8,
    subtitle: "Consulta tu primera tabla y entiende la anatomía de una consulta.",
    blocks: [
      { k: "p", text: "SQL (Structured Query Language) es el lenguaje estándar para comunicarse con bases de datos relacionales. Sirve para consultar, insertar, actualizar y borrar datos, y también para definir la estructura de las tablas." },
      { k: "p", text: "Una base de datos relacional guarda la información en tablas: filas (registros) y columnas (campos). En esta plataforma trabajarás con tres bases de ejemplo: `tienda`, `empleados` y `biblioteca`." },
      { k: "p", text: "La sentencia más usada es `SELECT`. Su forma más simple es:" },
      { k: "sql", db: "tienda", sql: "SELECT * FROM clientes;", caption: "El asterisco (*) significa “todas las columnas”. Ejecuta el ejemplo y verás las 8 filas de la tabla clientes." },
      { k: "list", items: [
        "`SELECT` indica qué columnas quieres ver.",
        "`FROM` indica de qué tabla se leen los datos.",
        "El punto y coma `;` marca el final de la sentencia."
      ] },
      { k: "note", text: "El orden lógico de lectura de SQL es FROM → WHERE → GROUP BY → HAVING → SELECT → ORDER BY → LIMIT, aunque se escriba empezando por SELECT." }
    ],
    exercise: {
      db: "tienda",
      prompt: "Obtén todas las filas y todas las columnas de la tabla `productos`.",
      initialSql: "-- Escribe aquí tu primera consulta\n",
      hint: "Usa SELECT * FROM seguido del nombre de la tabla y termina con punto y coma.",
      solution: "SELECT * FROM productos;",
      tests: [
        { label: "La consulta se ejecuta sin errores", check: (ctx) => ctx.out.ok === true },
        { label: "Devuelve exactamente 10 filas", check: (ctx) => (lastRows(ctx.out) || []).length === 10 },
        { label: "Incluye las 5 columnas de productos", check: (ctx) => { const r = lastRowsRes(ctx.out); return !!r && r.columns.length === 5; } }
      ]
    }
  },
  {
    id: "basico-2", level: "Básico", title: "Elegir columnas y DISTINCT", minutes: 7,
    subtitle: "Proyecta solo lo que necesitas y elimina duplicados.",
    blocks: [
      { k: "p", text: "En producción casi nunca querrás `SELECT *`: seleccionar solo las columnas necesarias reduce el tráfico y hace las consultas más claras." },
      { k: "sql", db: "tienda", sql: "SELECT nombre, categoria, precio FROM productos;", caption: "Las columnas se devuelven en el orden en que las escribes." },
      { k: "p", text: "`DISTINCT` elimina las filas repetidas del resultado:" },
      { k: "sql", db: "tienda", sql: "SELECT DISTINCT ciudad FROM clientes;", caption: "Sin DISTINCT, Madrid aparecería 3 veces." },
      { k: "note", text: "Puedes renombrar columnas con `AS`: SELECT precio AS precio_eur FROM productos;" }
    ],
    exercise: {
      db: "tienda",
      prompt: "Lista las ciudades distintas (sin repetir) en las que hay clientes. Debe devolver una sola columna llamada `ciudad`.",
      initialSql: "SELECT ...\n",
      hint: "Combina DISTINCT con la columna ciudad de la tabla clientes.",
      solution: "SELECT DISTINCT ciudad FROM clientes;",
      tests: [
        { label: "La consulta se ejecuta sin errores", check: (ctx) => ctx.out.ok === true },
        { label: "Devuelve exactamente 5 ciudades", check: (ctx) => (lastRows(ctx.out) || []).length === 5 },
        { label: "No hay valores duplicados", check: (ctx) => { const r = lastRows(ctx.out) || []; return new Set(r.map((x) => x[0])).size === r.length; } }
      ]
    }
  },
  {
    id: "basico-3", level: "Básico", title: "Filtrar filas con WHERE", minutes: 10,
    subtitle: "Operadores de comparación, AND, OR, LIKE, IN y BETWEEN.",
    blocks: [
      { k: "p", text: "La cláusula `WHERE` filtra filas: solo pasan las que cumplen la condición." },
      { k: "sql", db: "tienda", sql: "SELECT nombre, categoria, precio FROM productos WHERE precio < 50;", caption: "Operadores: =  <>  <  >  <=  >=" },
      { k: "sql", db: "tienda", sql: "SELECT nombre, precio FROM productos WHERE categoria = 'Accesorios' AND precio < 50;", caption: "Los textos van SIEMPRE entre comillas simples. Combina condiciones con AND / OR / NOT y paréntesis." },
      { k: "list", items: [
        "`LIKE 'A%'` coincide con textos que empiezan por A (% = cualquier cadena, _ = un carácter).",
        "`IN ('a', 'b')` equivale a varios OR.",
        "`BETWEEN 10 AND 20` es inclusivo en ambos extremos.",
        "`IS NULL` / `IS NOT NULL` comprueban valores nulos (nunca uses = NULL)."
      ] },
      { k: "sql", db: "biblioteca", sql: "SELECT id, libro_id, fecha_prestamo FROM prestamos WHERE fecha_devolucion IS NULL;", caption: "Préstamos todavía activos (fecha_devolucion es NULL)." }
    ],
    exercise: {
      db: "tienda",
      prompt: "Lista `nombre` y `precio` de los productos de la categoría 'Accesorios' que cuesten menos de 50.",
      initialSql: "SELECT nombre, precio\nFROM productos\nWHERE ...;\n",
      hint: "Necesitas dos condiciones unidas por AND: categoria = 'Accesorios' y precio < 50.",
      solution: "SELECT nombre, precio FROM productos WHERE categoria = 'Accesorios' AND precio < 50;",
      tests: [
        { label: "La consulta se ejecuta sin errores", check: (ctx) => ctx.out.ok === true },
        { label: "Devuelve exactamente 3 filas", check: (ctx) => (lastRows(ctx.out) || []).length === 3 },
        { label: "Todas las filas cuestan menos de 50", check: (ctx) => (lastRows(ctx.out) || []).every((r) => r[1] < 50) },
        { label: "Incluye 'Hub USB-C'", check: (ctx) => (lastRows(ctx.out) || []).some((r) => r[0] === "Hub USB-C") }
      ]
    }
  },
  {
    id: "basico-4", level: "Básico", title: "Ordenar y limitar: ORDER BY y LIMIT", minutes: 7,
    subtitle: "Presenta los resultados ordenados y quédate solo con los que necesitas.",
    blocks: [
      { k: "p", text: "`ORDER BY` ordena el resultado por una o más columnas, de forma ascendente (`ASC`, por defecto) o descendente (`DESC`)." },
      { k: "sql", db: "tienda", sql: "SELECT nombre, precio FROM productos ORDER BY precio DESC;", caption: "Del más caro al más barato." },
      { k: "p", text: "`LIMIT n` limita el número de filas; `OFFSET m` salta las m primeras filas (paginación)." },
      { k: "sql", db: "empleados", sql: "SELECT nombre, salario FROM empleados ORDER BY salario DESC LIMIT 3;", caption: "Los 3 salarios más altos." },
      { k: "note", text: "En ORDER BY puedes usar el alias de una columna de salida o su posición: ORDER BY 2 DESC." }
    ],
    exercise: {
      db: "tienda",
      prompt: "Obtén el top 3 de productos más caros: columnas `nombre` y `precio`, ordenadas de mayor a menor precio.",
      initialSql: "SELECT ...\nORDER BY ...\nLIMIT ...;\n",
      hint: "ORDER BY precio DESC LIMIT 3.",
      solution: "SELECT nombre, precio FROM productos ORDER BY precio DESC LIMIT 3;",
      tests: [
        { label: "La consulta se ejecuta sin errores", check: (ctx) => ctx.out.ok === true },
        { label: "Devuelve exactamente 3 filas", check: (ctx) => (lastRows(ctx.out) || []).length === 3 },
        { label: "La primera fila es 'Laptop Pro 14' (1299.99)", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.length > 0 && r[0][0] === "Laptop Pro 14" && near(r[0][1], 1299.99); } },
        { label: "Los precios van en orden descendente", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.every((row, i) => i === 0 || r[i - 1][1] >= row[1]); } }
      ]
    }
  },
  {
    id: "basico-5", level: "Básico", title: "Insertar datos: INSERT", minutes: 8,
    subtitle: "Añade filas nuevas respetando columnas y restricciones.",
    blocks: [
      { k: "p", text: "`INSERT INTO tabla (columnas) VALUES (valores);` añade filas nuevas. Indica siempre la lista de columnas: el código queda más claro y no depende del orden físico de la tabla." },
      { k: "sql", db: "tienda", sql: "INSERT INTO productos (id, nombre, categoria, precio, stock) VALUES (11, 'Lámpara LED', 'Hogar', 15.5, 40);", preview: "SELECT * FROM productos WHERE id = 11;", caption: "INSERT seguido de un SELECT para comprobar la fila creada (se ejecuta sobre una copia de la base de datos)." },
      { k: "p", text: "Puedes insertar varias filas en una sola sentencia separando las tuplas por comas: `VALUES (1,'a'), (2,'b');`." },
      { k: "note", text: "Si una columna es NOT NULL o PRIMARY KEY, debes darle un valor (o depender de AUTOINCREMENT). Si duplicas una clave primaria, el motor devuelve un error explicativo." }
    ],
    exercise: {
      db: "tienda",
      prompt: "Inserta una clienta nueva: id 9, nombre 'Elena Prado', ciudad 'Zaragoza', email 'elena@example.com' y fecha_registro '2024-09-01'.",
      initialSql: "INSERT INTO clientes (id, nombre, ciudad, email, fecha_registro)\nVALUES (...);\n",
      hint: "Cinco columnas, cinco valores. Los textos entre comillas simples.",
      solution: "INSERT INTO clientes (id, nombre, ciudad, email, fecha_registro) VALUES (9, 'Elena Prado', 'Zaragoza', 'elena@example.com', '2024-09-01');",
      tests: [
        { label: "La sentencia se ejecuta sin errores", check: (ctx) => ctx.out.ok === true },
        { label: "La tabla clientes pasa a tener 9 filas", check: (ctx) => tbl(ctx.db, "clientes").rows.length === 9 },
        { label: "Existe una fila con nombre 'Elena Prado'", check: (ctx) => tbl(ctx.db, "clientes").rows.some((r) => r.nombre === "Elena Prado" && r.ciudad === "Zaragoza") }
      ]
    }
  },
  {
    id: "intermedio-1", level: "Intermedio", title: "Modificar y borrar: UPDATE y DELETE", minutes: 9,
    subtitle: "Cambia y elimina datos… sin destruir la tabla entera.",
    blocks: [
      { k: "p", text: "`UPDATE tabla SET columna = valor WHERE condicion;` modifica las filas que cumplen la condición." },
      { k: "sql", db: "tienda", sql: "UPDATE productos SET precio = ROUND(precio * 1.1, 2) WHERE categoria = 'Audio';", preview: "SELECT nombre, precio FROM productos WHERE categoria = 'Audio';", caption: "Sube un 10% el precio de los productos de Audio." },
      { k: "p", text: "`DELETE FROM tabla WHERE condicion;` borra filas. Sin WHERE, borra TODA la tabla (el editor te avisará)." },
      { k: "sql", db: "tienda", sql: "DELETE FROM pedidos WHERE estado = 'pendiente';", preview: "SELECT COUNT(*) AS pedidos_restantes FROM pedidos;", caption: "Se eliminan los 3 pedidos pendientes." },
      { k: "note", text: "Regla de oro: escribe primero el WHERE como un SELECT para ver qué filas afectarías. En producción, agrupa varios cambios dentro de una transacción (BEGIN/COMMIT/ROLLBACK)." }
    ],
    exercise: {
      db: "tienda",
      prompt: "En un solo script (dos sentencias): 1) rebaja un 10% (redondeado a 2 decimales) el precio de los productos de 'Audio'; 2) elimina los clientes de 'Bilbao'.",
      initialSql: "UPDATE ...\n;\nDELETE ...\n;\n",
      hint: "UPDATE productos SET precio = ROUND(precio * 0.9, 2) WHERE categoria = 'Audio'; y DELETE FROM clientes WHERE ciudad = 'Bilbao';",
      solution: "UPDATE productos SET precio = ROUND(precio * 0.9, 2) WHERE categoria = 'Audio';\nDELETE FROM clientes WHERE ciudad = 'Bilbao';",
      tests: [
        { label: "El script se ejecuta sin errores", check: (ctx) => ctx.out.ok === true },
        { label: "Auriculares BT pasa a costar ~53.99", check: (ctx) => { const p = tbl(ctx.db, "productos").rows.find((r) => r.id === 8); return !!p && near(p.precio, 53.99, 0.02); } },
        { label: "Solo quedan 7 clientes", check: (ctx) => tbl(ctx.db, "clientes").rows.length === 7 },
        { label: "Ya no hay clientes en Bilbao", check: (ctx) => !tbl(ctx.db, "clientes").rows.some((r) => r.ciudad === "Bilbao") }
      ]
    }
  },
  {
    id: "intermedio-2", level: "Intermedio", title: "Combinar tablas: JOIN", minutes: 12,
    subtitle: "INNER, LEFT, RIGHT y CROSS JOIN con claves foráneas.",
    blocks: [
      { k: "p", text: "Las bases de datos relacionales reparten la información en varias tablas conectadas por claves. `pedidos.cliente_id` referencia a `clientes.id`: eso es una clave foránea." },
      { k: "sql", db: "tienda", sql: "SELECT p.id AS pedido, c.nombre AS cliente, p.fecha\nFROM pedidos p\nJOIN clientes c ON c.id = p.cliente_id;", caption: "INNER JOIN (o simplemente JOIN): solo filas con coincidencia en ambas tablas." },
      { k: "sql", db: "empleados", sql: "SELECT e.nombre, a.proyecto_id, a.horas\nFROM empleados e\nLEFT JOIN asignaciones a ON a.empleado_id = e.id;", caption: "LEFT JOIN: conserva TODAS las filas de la izquierda; si no hay coincidencia, rellena con NULL (Andrés Cano no tiene asignaciones)." },
      { k: "list", items: [
        "`INNER JOIN` — intersección: filas con coincidencia en ambas tablas.",
        "`LEFT JOIN` — todo el lado izquierdo + coincidencias del derecho.",
        "`RIGHT JOIN` — todo el lado derecho + coincidencias del izquierdo.",
        "`CROSS JOIN` — producto cartesiano (todas las combinaciones)."
      ] },
      { k: "note", text: "Usa alias de tabla (p, c, e…) y cualifica las columnas compartidas: p.id frente a c.id. Si no lo haces y la columna existe en dos tablas, recibirás un error de “columna ambigua”." }
    ],
    exercise: {
      db: "tienda",
      prompt: "Lista cada pedido con el nombre de su cliente: columnas `p.id`, `c.nombre` y `p.fecha`, ordenadas por id de pedido.",
      initialSql: "SELECT p.id, c.nombre, p.fecha\nFROM pedidos p\nJOIN clientes c ON ...\nORDER BY p.id;\n",
      hint: "La condición del JOIN es c.id = p.cliente_id.",
      solution: "SELECT p.id, c.nombre, p.fecha FROM pedidos p JOIN clientes c ON c.id = p.cliente_id ORDER BY p.id;",
      tests: [
        { label: "La consulta se ejecuta sin errores", check: (ctx) => ctx.out.ok === true },
        { label: "Devuelve 12 filas (todos los pedidos)", check: (ctx) => (lastRows(ctx.out) || []).length === 12 },
        { label: "3 columnas en el resultado", check: (ctx) => { const r = lastRowsRes(ctx.out); return !!r && r.columns.length === 3; } },
        { label: "El pedido 1 es de Ana García (2024-01-10)", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.length > 0 && r[0][0] === 1 && r[0][1] === "Ana García" && r[0][2] === "2024-01-10"; } }
      ]
    }
  },
  {
    id: "intermedio-3", level: "Intermedio", title: "Agrupar y agregar: GROUP BY y HAVING", minutes: 11,
    subtitle: "COUNT, SUM, AVG, MIN y MAX para convertir filas en métricas.",
    blocks: [
      { k: "p", text: "Las funciones de agregado resumen muchas filas en un valor: `COUNT`, `SUM`, `AVG`, `MIN` y `MAX`." },
      { k: "sql", db: "tienda", sql: "SELECT COUNT(*) AS productos, ROUND(AVG(precio), 2) AS precio_medio, MAX(precio) AS maximo FROM productos;", caption: "Un agregado sin GROUP BY resume TODA la tabla en una fila." },
      { k: "p", text: "`GROUP BY` agrupa las filas por un valor y calcula el agregado por grupo:" },
      { k: "sql", db: "tienda", sql: "SELECT cliente_id, COUNT(*) AS pedidos\nFROM pedidos\nGROUP BY cliente_id\nORDER BY pedidos DESC;", caption: "Número de pedidos por cliente." },
      { k: "p", text: "`HAVING` filtra GRUPOS (WHERE filtra filas y no puede usar agregados):" },
      { k: "sql", db: "tienda", sql: "SELECT cliente_id, COUNT(*) AS pedidos\nFROM pedidos\nGROUP BY cliente_id\nHAVING COUNT(*) >= 2;", caption: "Solo clientes con 2 o más pedidos." }
    ],
    exercise: {
      db: "tienda",
      prompt: "Calcula la facturación por producto: `producto_id` y `SUM(cantidad * precio_unitario)` con alias `total`, sobre `detalle_pedidos`, agrupado por producto_id y ordenado por total descendente.",
      initialSql: "SELECT producto_id, SUM(cantidad * precio_unitario) AS total\nFROM detalle_pedidos\nGROUP BY ...\nORDER BY ...;\n",
      hint: "GROUP BY producto_id ORDER BY total DESC.",
      solution: "SELECT producto_id, SUM(cantidad * precio_unitario) AS total FROM detalle_pedidos GROUP BY producto_id ORDER BY total DESC;",
      tests: [
        { label: "La consulta se ejecuta sin errores", check: (ctx) => ctx.out.ok === true },
        { label: "Devuelve 10 grupos (uno por producto vendido)", check: (ctx) => (lastRows(ctx.out) || []).length === 10 },
        { label: "El producto 1 encabeza el ranking", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.length > 0 && r[0][0] === 1 && near(r[0][1], 3899.97, 0.05); } },
        { label: "Totales en orden descendente", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.every((row, i) => i === 0 || r[i - 1][1] >= row[1]); } }
      ]
    }
  },
  {
    id: "intermedio-4", level: "Intermedio", title: "Subconsultas", minutes: 10,
    subtitle: "Consultas dentro de consultas: escalares, IN y EXISTS.",
    blocks: [
      { k: "p", text: "Una subconsulta es un `SELECT` dentro de otra sentencia. Si devuelve un único valor se llama subconsulta escalar:" },
      { k: "sql", db: "tienda", sql: "SELECT nombre, precio\nFROM productos\nWHERE precio > (SELECT AVG(precio) FROM productos);", caption: "Productos por encima del precio medio (el medio se calcula primero: 200.88)." },
      { k: "p", text: "Con `IN (SELECT ...)` comparas contra un conjunto de valores:" },
      { k: "sql", db: "tienda", sql: "SELECT nombre FROM clientes\nWHERE id IN (SELECT cliente_id FROM pedidos WHERE estado = 'pendiente');", caption: "Clientes con algún pedido pendiente." },
      { k: "p", text: "`EXISTS (SELECT ...)` comprueba si la subconsulta devuelve al menos una fila." },
      { k: "note", text: "Limitación del sandbox: no se admiten subconsultas correlacionadas (que referencian columnas de la consulta externa). Como alternativa, usa JOIN o tablas derivadas, que verás en el nivel avanzado." }
    ],
    exercise: {
      db: "tienda",
      prompt: "Lista `nombre` y `precio` de los productos cuyo precio supera al precio medio de TODOS los productos, ordenados por precio descendente.",
      initialSql: "SELECT nombre, precio\nFROM productos\nWHERE precio > (SELECT ...)\nORDER BY precio DESC;\n",
      hint: "La subconsulta es (SELECT AVG(precio) FROM productos).",
      solution: "SELECT nombre, precio FROM productos WHERE precio > (SELECT AVG(precio) FROM productos) ORDER BY precio DESC;",
      tests: [
        { label: "La consulta se ejecuta sin errores", check: (ctx) => ctx.out.ok === true },
        { label: "Devuelve exactamente 2 filas", check: (ctx) => (lastRows(ctx.out) || []).length === 2 },
        { label: "La primera fila es 'Laptop Pro 14'", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.length > 0 && r[0][0] === "Laptop Pro 14"; } },
        { label: "La segunda fila es 'Monitor 27\"'", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.length > 1 && r[1][0] === 'Monitor 27"'; } }
      ]
    }
  },
  {
    id: "avanzado-1", level: "Avanzado", title: "Tablas derivadas (subconsultas en FROM)", minutes: 10,
    subtitle: "Trata el resultado de una consulta como si fuera una tabla.",
    blocks: [
      { k: "p", text: "Una subconsulta en `FROM` (tabla derivada) permite JOINear contra resultados agregados. Siempre necesita un alias." },
      { k: "sql", db: "empleados", sql: "SELECT d.nombre AS departamento, ROUND(m.media, 2) AS salario_medio\nFROM departamentos d\nJOIN (SELECT departamento_id, AVG(salario) AS media\n      FROM empleados\n      GROUP BY departamento_id) m\n  ON m.departamento_id = d.id\nORDER BY m.media DESC;", caption: "Salario medio por departamento, con JOIN sobre la tabla derivada m." },
      { k: "note", text: "Las tablas derivadas sustituyen a las subconsultas correlacionadas, que el sandbox no soporta: agrega primero, JOINea después." }
    ],
    exercise: {
      db: "empleados",
      prompt: "Lista `nombre` y `salario` de los empleados que cobran MÁS que la media de su departamento, ordenados por nombre. Usa una tabla derivada con AVG(salario) por departamento_id.",
      initialSql: "SELECT e.nombre, e.salario\nFROM empleados e\nJOIN (SELECT departamento_id, AVG(salario) AS media\n      FROM empleados\n      GROUP BY departamento_id) d\n  ON ...\nWHERE ...\nORDER BY e.nombre;\n",
      hint: "ON e.departamento_id = d.departamento_id WHERE e.salario > d.media.",
      solution: "SELECT e.nombre, e.salario FROM empleados e JOIN (SELECT departamento_id, AVG(salario) AS media FROM empleados GROUP BY departamento_id) d ON e.departamento_id = d.departamento_id WHERE e.salario > d.media ORDER BY e.nombre;",
      tests: [
        { label: "La consulta se ejecuta sin errores", check: (ctx) => ctx.out.ok === true },
        { label: "Devuelve exactamente 4 empleados", check: (ctx) => (lastRows(ctx.out) || []).length === 4 },
        { label: "La primera fila es 'Ana Pérez'", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.length > 0 && r[0][0] === "Ana Pérez"; } },
        { label: "Incluye a 'Hugo Marín'", check: (ctx) => (lastRows(ctx.out) || []).some((r) => r[0] === "Hugo Marín") }
      ]
    }
  },
  {
    id: "avanzado-2", level: "Avanzado", title: "Expresiones CASE", minutes: 8,
    subtitle: "Lógica condicional dentro del SELECT.",
    blocks: [
      { k: "p", text: "`CASE` devuelve un valor según condiciones. Es el “if/else” de SQL y funciona en SELECT, ORDER BY, WHERE…" },
      { k: "sql", db: "tienda", sql: "SELECT nombre, precio,\n       CASE WHEN precio > 500 THEN 'alto'\n            WHEN precio >= 50 THEN 'medio'\n            ELSE 'bajo' END AS gama\nFROM productos\nORDER BY precio DESC;", caption: "Clasifica cada producto en una gama de precio." },
      { k: "p", text: "También existe el CASE simple: `CASE categoria WHEN 'Audio' THEN ... END`, que compara un valor contra cada WHEN." }
    ],
    exercise: {
      db: "tienda",
      prompt: "Para cada producto muestra `nombre` y una columna `gama` con CASE: 'alto' si precio > 500, 'medio' si precio >= 50 y 'bajo' en otro caso. Ordena por precio descendente.",
      initialSql: "SELECT nombre,\n       CASE WHEN ... END AS gama\nFROM productos\nORDER BY precio DESC;\n",
      hint: "Recuerda cerrar la expresión con END y ponerle alias con AS gama.",
      solution: "SELECT nombre, CASE WHEN precio > 500 THEN 'alto' WHEN precio >= 50 THEN 'medio' ELSE 'bajo' END AS gama FROM productos ORDER BY precio DESC;",
      tests: [
        { label: "La consulta se ejecuta sin errores", check: (ctx) => ctx.out.ok === true },
        { label: "Devuelve 10 filas", check: (ctx) => (lastRows(ctx.out) || []).length === 10 },
        { label: "'Laptop Pro 14' es de gama 'alto'", check: (ctx) => { const r = (lastRows(ctx.out) || []).find((x) => x[0] === "Laptop Pro 14"); return !!r && r[1] === "alto"; } },
        { label: "'Mouse Inalámbrico' es de gama 'bajo'", check: (ctx) => { const r = (lastRows(ctx.out) || []).find((x) => x[0] === "Mouse Inalámbrico"); return !!r && r[1] === "bajo"; } }
      ]
    }
  },
  {
    id: "avanzado-3", level: "Avanzado", title: "CTE: consultas con WITH", minutes: 10,
    subtitle: "Da nombre a resultados intermedios para consultas legibles.",
    blocks: [
      { k: "p", text: "Un CTE (Common Table Expression) define una consulta con nombre que solo existe durante la ejecución. Se declara con `WITH nombre AS ( SELECT ... )` antes del SELECT principal." },
      { k: "sql", db: "tienda", sql: "WITH ingresos AS (\n  SELECT pedido_id, SUM(cantidad * precio_unitario) AS total\n  FROM detalle_pedidos\n  GROUP BY pedido_id\n)\nSELECT pedido_id, ROUND(total, 2) AS total\nFROM ingresos\nORDER BY total DESC\nLIMIT 5;", caption: "Top 5 de pedidos por importe. El CTE hace la consulta mucho más legible que una subconsulta anidada." },
      { k: "p", text: "Puedes encadenar varios CTE separados por comas; cada uno puede usar los anteriores: `WITH a AS (...), b AS (SELECT ... FROM a) SELECT * FROM b;`" }
    ],
    exercise: {
      db: "tienda",
      prompt: "Usa un CTE llamado `ingresos` con el total facturado por pedido (SUM(cantidad * precio_unitario) agrupado por pedido_id) y después selecciona `pedido_id` y `ROUND(total, 2) AS total` solo de los pedidos con total > 200, ordenados por total descendente.",
      initialSql: "WITH ingresos AS (\n  SELECT ...\n)\nSELECT ...\nFROM ingresos\nWHERE total > 200\nORDER BY total DESC;\n",
      hint: "El CTE agrupa detalle_pedidos por pedido_id; la consulta externa filtra por total > 200.",
      solution: "WITH ingresos AS (SELECT pedido_id, SUM(cantidad * precio_unitario) AS total FROM detalle_pedidos GROUP BY pedido_id) SELECT pedido_id, ROUND(total, 2) AS total FROM ingresos WHERE total > 200 ORDER BY total DESC;",
      tests: [
        { label: "La consulta se ejecuta sin errores", check: (ctx) => ctx.out.ok === true },
        { label: "Devuelve exactamente 6 pedidos", check: (ctx) => (lastRows(ctx.out) || []).length === 6 },
        { label: "El pedido 12 encabeza la lista (~1365.49)", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.length > 0 && r[0][0] === 12 && near(r[0][1], 1365.49, 0.05); } }
      ]
    }
  },
  {
    id: "avanzado-4", level: "Avanzado", title: "UNION, INTERSECT y EXCEPT", minutes: 8,
    subtitle: "Combina los resultados de varias consultas.",
    blocks: [
      { k: "p", text: "Las operaciones de conjunto combinan los resultados de dos SELECT con el mismo número de columnas:" },
      { k: "list", items: [
        "`UNION` — une y elimina duplicados.",
        "`UNION ALL` — une conservando duplicados (más rápido).",
        "`INTERSECT` — solo las filas comunes a ambos resultados.",
        "`EXCEPT` — las filas del primero que no están en el segundo."
      ] },
      { k: "sql", db: "empleados", sql: "SELECT nombre FROM empleados WHERE departamento_id = 1\nUNION\nSELECT nombre FROM empleados WHERE departamento_id = 2\nORDER BY nombre;", caption: "Nombres de Ingeniería y Ventas, sin duplicados y ordenados." }
    ],
    exercise: {
      db: "tienda",
      prompt: "Construye una única lista ordenada de nombres: los clientes de 'Madrid' (UNION) los empleados cuyo puesto empiece por 'Comercial'. Columna `nombre`, sin duplicados.",
      initialSql: "SELECT nombre FROM clientes WHERE ciudad = 'Madrid'\nUNION\nSELECT nombre FROM empleados WHERE puesto LIKE ...\nORDER BY nombre;\n",
      hint: "puesto LIKE 'Comercial%'. Ojo: clientes y empleados están en bases distintas; este ejercicio usa la base 'tienda'… ¡corrige el segundo SELECT para usar la tabla que exista aquí! En la base tienda no hay empleados: usa como segunda lista los clientes de 'Valencia'.",
      solution: "SELECT nombre FROM clientes WHERE ciudad = 'Madrid' UNION SELECT nombre FROM clientes WHERE ciudad = 'Valencia' ORDER BY nombre;",
      tests: [
        { label: "La consulta se ejecuta sin errores", check: (ctx) => ctx.out.ok === true },
        { label: "Devuelve exactamente 5 filas", check: (ctx) => (lastRows(ctx.out) || []).length === 5 },
        { label: "Incluye 'Ana García' y 'Carlos Ruiz'", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.some((x) => x[0] === "Ana García") && r.some((x) => x[0] === "Carlos Ruiz"); } },
        { label: "Sin duplicados", check: (ctx) => { const r = lastRows(ctx.out) || []; return new Set(r.map((x) => x[0])).size === r.length; } }
      ]
    }
  },
  {
    id: "avanzado-5", level: "Avanzado", title: "Transacciones e integridad", minutes: 9,
    subtitle: "BEGIN, COMMIT y ROLLBACK: cambios atómicos y seguros.",
    blocks: [
      { k: "p", text: "Una transacción agrupa varios cambios como una unidad ATÓMICA: o se aplican todos (COMMIT) o ninguno (ROLLBACK). Es la base de las propiedades ACID de los SGBD." },
      { k: "sql", db: "tienda", sql: "BEGIN;\nUPDATE productos SET precio = 0;\nROLLBACK;\nSELECT COUNT(*) AS precios_a_cero FROM productos WHERE precio = 0;", caption: "El UPDATE llega a ejecutarse, pero ROLLBACK lo revierte: el recuento final es 0." },
      { k: "list", items: [
        "`BEGIN;` abre la transacción (en el sandbox se guarda una instantánea).",
        "`COMMIT;` hace permanentes los cambios.",
        "`ROLLBACK;` restaura la instantánea y descarta los cambios."
      ] },
      { k: "p", text: "La integridad se protege con restricciones: PRIMARY KEY (identidad única), NOT NULL, UNIQUE y FOREIGN KEY (referencias válidas). El sandbox aplica PK, NOT NULL y UNIQUE; los índices, que aceleran las búsquedas, son transparentes para el resultado de las consultas." }
    ],
    exercise: {
      db: "tienda",
      prompt: "Demuestra que una transacción protege los datos: en un solo script abre una transacción, pon todos los precios a 1, revierte la transacción y comprueba con un SELECT COUNT(*) cuántos productos tienen precio < 2 (debe ser 0).",
      initialSql: "BEGIN;\nUPDATE ...;\nROLLBACK;\nSELECT COUNT(*) AS modificados FROM productos WHERE precio < 2;\n",
      hint: "BEGIN; UPDATE productos SET precio = 1; ROLLBACK; SELECT COUNT(*) AS modificados FROM productos WHERE precio < 2;",
      solution: "BEGIN;\nUPDATE productos SET precio = 1;\nROLLBACK;\nSELECT COUNT(*) AS modificados FROM productos WHERE precio < 2;",
      tests: [
        { label: "El script se ejecuta sin errores", check: (ctx) => ctx.out.ok === true },
        { label: "El recuento final es 0", check: (ctx) => { const r = lastRows(ctx.out); return !!r && r.length === 1 && r[0][0] === 0; } },
        { label: "El precio del producto 1 sigue siendo 1299.99", check: (ctx) => { const p = tbl(ctx.db, "productos").rows.find((x) => x.id === 1); return !!p && near(p.precio, 1299.99); } }
      ]
    }
  }
];

const CHALLENGES = [
  {
    id: "d1", level: "Básico", db: "tienda", title: "Informe de stock bajo",
    intro: "El equipo de logística necesita un informe con los productos que tienen menos de 50 unidades en almacén.",
    goals: ["Columnas: nombre, categoria y stock", "Solo productos con stock < 50", "Ordenados de menos a más stock"],
    initialSql: "-- Informe de stock bajo\nSELECT ...\n",
    hint: "WHERE stock < 50 ORDER BY stock ASC.",
    solution: "SELECT nombre, categoria, stock FROM productos WHERE stock < 50 ORDER BY stock ASC;",
    tests: [
      { label: "Se ejecuta sin errores", check: (ctx) => ctx.out.ok },
      { label: "Devuelve exactamente 2 filas", check: (ctx) => (lastRows(ctx.out) || []).length === 2 },
      { label: "Primera fila: Laptop Pro 14 / Electrónica / 25", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.length > 0 && JSON.stringify(r[0]) === JSON.stringify(["Laptop Pro 14", "Electrónica", 25]); } },
      { label: "Segunda fila: Monitor 27\" / Electrónica / 40", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.length > 1 && JSON.stringify(r[1]) === JSON.stringify(['Monitor 27"', "Electrónica", 40]); } }
    ]
  },
  {
    id: "d2", level: "Básico", db: "tienda", title: "Alta de cliente y verificación",
    intro: "Registra a una nueva clienta y verifica el alta con un recuento: Elena Prado, id 9, ciudad Zaragoza, email elena@example.com, fecha_registro 2024-09-01.",
    goals: ["INSERT con las 5 columnas", "SELECT COUNT(*) final para verificar"],
    initialSql: "INSERT INTO clientes (id, nombre, ciudad, email, fecha_registro)\nVALUES (...);\n\nSELECT COUNT(*) AS total FROM clientes;\n",
    hint: "Después del INSERT, un SELECT COUNT(*) AS total FROM clientes; debe devolver 9.",
    solution: "INSERT INTO clientes (id, nombre, ciudad, email, fecha_registro) VALUES (9, 'Elena Prado', 'Zaragoza', 'elena@example.com', '2024-09-01');\nSELECT COUNT(*) AS total FROM clientes;",
    tests: [
      { label: "El script se ejecuta sin errores", check: (ctx) => ctx.out.ok },
      { label: "El recuento final es 9", check: (ctx) => { const r = lastRows(ctx.out); return !!r && r[0][0] === 9; } },
      { label: "Elena Prado está en la tabla con email correcto", check: (ctx) => tbl(ctx.db, "clientes").rows.some((x) => x.nombre === "Elena Prado" && x.email === "elena@example.com") }
    ]
  },
  {
    id: "d3", level: "Intermedio", db: "tienda", title: "Clientes y su número de pedidos",
    intro: "Marketing quiere saber cuántos pedidos ha hecho cada cliente. Deben aparecer TODOS los clientes, incluso los que nunca han pedido.",
    goals: ["Columnas: nombre (del cliente) y pedidos (recuento)", "LEFT JOIN de clientes a pedidos", "GROUP BY por cliente", "Orden: más pedidos primero y, a igualdad, por nombre"],
    initialSql: "SELECT c.nombre, COUNT(p.id) AS pedidos\nFROM clientes c\nLEFT JOIN pedidos p ON ...\nGROUP BY ...\nORDER BY ...;\n",
    hint: "COUNT(p.id) no cuenta los NULL de clientes sin pedidos. ORDER BY pedidos DESC, c.nombre.",
    solution: "SELECT c.nombre, COUNT(p.id) AS pedidos FROM clientes c LEFT JOIN pedidos p ON p.cliente_id = c.id GROUP BY c.nombre ORDER BY pedidos DESC, c.nombre;",
    tests: [
      { label: "Se ejecuta sin errores", check: (ctx) => ctx.out.ok },
      { label: "Devuelve 8 filas (todos los clientes)", check: (ctx) => (lastRows(ctx.out) || []).length === 8 },
      { label: "Primera fila: Ana García con 3 pedidos", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.length > 0 && r[0][0] === "Ana García" && r[0][1] === 3; } },
      { label: "Segunda fila: Luis Martínez con 2 pedidos", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.length > 1 && r[1][0] === "Luis Martínez" && r[1][1] === 2; } }
    ]
  },
  {
    id: "d4", level: "Intermedio", db: "tienda", title: "Facturación por categoría",
    intro: "Dirección pide la facturación total por categoría de producto (importe = cantidad × precio_unitario de cada línea de pedido).",
    goals: ["JOIN de detalle_pedidos con productos", "Columnas: categoria e ingresos (SUM redondeado a 2 decimales)", "GROUP BY categoria", "Ordenado por ingresos descendente"],
    initialSql: "SELECT p.categoria, ROUND(SUM(d.cantidad * d.precio_unitario), 2) AS ingresos\nFROM detalle_pedidos d\nJOIN productos p ON ...\nGROUP BY ...\nORDER BY ...;\n",
    hint: "JOIN por p.id = d.producto_id; GROUP BY p.categoria.",
    solution: "SELECT p.categoria, ROUND(SUM(d.cantidad * d.precio_unitario), 2) AS ingresos FROM detalle_pedidos d JOIN productos p ON p.id = d.producto_id GROUP BY p.categoria ORDER BY ingresos DESC;",
    tests: [
      { label: "Se ejecuta sin errores", check: (ctx) => ctx.out.ok },
      { label: "Devuelve 4 categorías", check: (ctx) => (lastRows(ctx.out) || []).length === 4 },
      { label: "Electrónica lidera con ~4646.97", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.length > 0 && r[0][0] === "Electrónica" && near(r[0][1], 4646.97, 0.05); } },
      { label: "Ingresos en orden descendente", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.every((row, i) => i === 0 || r[i - 1][1] >= row[1]); } }
    ]
  },
  {
    id: "d5", level: "Intermedio", db: "biblioteca", title: "Préstamos por libro y autor",
    intro: "La biblioteca quiere un ranking de préstamos por libro, mostrando también el nombre del autor. Los libros nunca prestados también deben aparecer (con 0).",
    goals: ["Columnas: titulo, autor (nombre) y prestamos (recuento)", "JOIN libros→autores y LEFT JOIN libros→prestamos", "GROUP BY por libro", "Orden: más prestados primero y desempate por título"],
    initialSql: "SELECT l.titulo, a.nombre AS autor, COUNT(p.id) AS prestamos\nFROM libros l\nJOIN autores a ON a.id = l.autor_id\nLEFT JOIN prestamos p ON ...\nGROUP BY l.titulo, a.nombre\nORDER BY ...;\n",
    hint: "COUNT(p.id) devuelve 0 cuando no hay préstamos (los NULL no cuentan). ORDER BY prestamos DESC, l.titulo.",
    solution: "SELECT l.titulo, a.nombre AS autor, COUNT(p.id) AS prestamos FROM libros l JOIN autores a ON a.id = l.autor_id LEFT JOIN prestamos p ON p.libro_id = l.id GROUP BY l.titulo, a.nombre ORDER BY prestamos DESC, l.titulo;",
    tests: [
      { label: "Se ejecuta sin errores", check: (ctx) => ctx.out.ok },
      { label: "Devuelve 8 filas (todos los libros)", check: (ctx) => (lastRows(ctx.out) || []).length === 8 },
      { label: "Primera fila: Cien años de soledad / Gabriel García Márquez / 2", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.length > 0 && r[0][0] === "Cien años de soledad" && r[0][2] === 2; } },
      { label: "Segunda fila: Ficciones / Jorge Luis Borges / 2", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.length > 1 && r[1][0] === "Ficciones" && r[1][2] === 2; } }
    ]
  },
  {
    id: "d6", level: "Avanzado", db: "biblioteca", title: "Top 3 con CTE",
    intro: "Repite el ranking de préstamos, pero esta vez calculando el recuento en un CTE llamado `ranking` y uniéndolo después con libros. Quédate solo con el top 3.",
    goals: ["CTE ranking: libro_id y veces (COUNT agrupado)", "JOIN del CTE con libros", "Columnas: titulo y veces", "ORDER BY veces DESC, titulo y LIMIT 3"],
    initialSql: "WITH ranking AS (\n  SELECT libro_id, COUNT(*) AS veces\n  FROM prestamos\n  GROUP BY libro_id\n)\nSELECT l.titulo, r.veces\nFROM ranking r\nJOIN libros l ON l.id = r.libro_id\nORDER BY ...\nLIMIT 3;\n",
    hint: "ORDER BY r.veces DESC, l.titulo LIMIT 3.",
    solution: "WITH ranking AS (SELECT libro_id, COUNT(*) AS veces FROM prestamos GROUP BY libro_id) SELECT l.titulo, r.veces FROM ranking r JOIN libros l ON l.id = r.libro_id ORDER BY r.veces DESC, l.titulo LIMIT 3;",
    tests: [
      { label: "Se ejecuta sin errores", check: (ctx) => ctx.out.ok },
      { label: "Devuelve exactamente 3 filas", check: (ctx) => (lastRows(ctx.out) || []).length === 3 },
      { label: "Los dos primeros tienen 2 préstamos", check: (ctx) => { const r = lastRows(ctx.out) || []; return r.length > 1 && r[0][1] === 2 && r[1][1] === 2; } },
      { label: "El top 2 son 'Cien años de soledad' y 'Ficciones'", check: (ctx) => { const r = lastRows(ctx.out) || []; const s = new Set([r[0] && r[0][0], r[1] && r[1][0]]); return s.has("Cien años de soledad") && s.has("Ficciones"); } }
    ]
  },
  {
    id: "d7", level: "Avanzado", db: "tienda", title: "Simulación segura con transacciones",
    intro: "Antes de una limpieza de datos quieres simular un borrado masivo sin consecuencias: borra TODAS las líneas de pedido dentro de una transacción, revierte el cambio y demuestra que los datos siguen intactos.",
    goals: ["BEGIN; DELETE FROM detalle_pedidos; ROLLBACK;", "SELECT COUNT(*) final que demuestre que hay 20 filas"],
    initialSql: "BEGIN;\nDELETE FROM detalle_pedidos;\nROLLBACK;\nSELECT COUNT(*) AS filas FROM detalle_pedidos;\n",
    hint: "El ROLLBACK debe ir antes del SELECT de verificación.",
    solution: "BEGIN;\nDELETE FROM detalle_pedidos;\nROLLBACK;\nSELECT COUNT(*) AS filas FROM detalle_pedidos;",
    tests: [
      { label: "El script se ejecuta sin errores", check: (ctx) => ctx.out.ok },
      { label: "El recuento final es 20", check: (ctx) => { const r = lastRows(ctx.out); return !!r && r[0][0] === 20; } },
      { label: "La tabla sigue teniendo 20 filas en la BD", check: (ctx) => tbl(ctx.db, "detalle_pedidos").rows.length === 20 },
      { label: "Se informó del ROLLBACK", check: (ctx) => ctx.out.messages.some((m) => m.text.indexOf("ROLLBACK") !== -1) }
    ]
  }
];

const CHEATSHEET = [
  { cat: "Consultas", cmd: "SELECT *", syntax: "SELECT * FROM tabla;", desc: "Todas las columnas y filas de una tabla.", example: "SELECT * FROM clientes LIMIT 5;", db: "tienda" },
  { cat: "Consultas", cmd: "SELECT columnas", syntax: "SELECT col1, col2 FROM tabla;", desc: "Proyecta solo las columnas que necesitas, en el orden indicado.", example: "SELECT nombre, categoria, precio FROM productos;", db: "tienda" },
  { cat: "Consultas", cmd: "DISTINCT", syntax: "SELECT DISTINCT col FROM tabla;", desc: "Elimina filas duplicadas del resultado.", example: "SELECT DISTINCT ciudad FROM clientes;", db: "tienda" },
  { cat: "Consultas", cmd: "Alias (AS)", syntax: "SELECT col AS alias FROM tabla t;", desc: "Renombra columnas y tablas temporalmente.", example: "SELECT nombre AS producto, ROUND(precio * 1.21, 2) AS precio_iva FROM productos LIMIT 5;", db: "tienda" },
  { cat: "Filtrado", cmd: "WHERE", syntax: "SELECT ... FROM tabla WHERE condicion;", desc: "Filtra filas por una condición.", example: "SELECT nombre, precio FROM productos WHERE precio > 50;", db: "tienda" },
  { cat: "Filtrado", cmd: "AND / OR / NOT", syntax: "WHERE cond1 AND (cond2 OR cond3);", desc: "Combina condiciones; los paréntesis fijan la prioridad.", example: "SELECT nombre FROM productos WHERE categoria = 'Audio' AND NOT precio > 50;", db: "tienda" },
  { cat: "Filtrado", cmd: "Operadores", syntax: "=  <>  <  >  <=  >=", desc: "Comparaciones. <> (o !=) significa “distinto de”.", example: "SELECT nombre, salario FROM empleados WHERE salario >= 50000;", db: "empleados" },
  { cat: "Filtrado", cmd: "LIKE", syntax: "WHERE texto LIKE 'patron%';", desc: "% = cualquier cadena; _ = un carácter. No distingue mayúsculas.", example: "SELECT nombre FROM clientes WHERE nombre LIKE 'a%';", db: "tienda" },
  { cat: "Filtrado", cmd: "IN", syntax: "WHERE col IN (v1, v2, ...);", desc: "Coincide con cualquiera de los valores (o de una subconsulta).", example: "SELECT nombre, precio FROM productos WHERE categoria IN ('Audio', 'Accesorios');", db: "tienda" },
  { cat: "Filtrado", cmd: "BETWEEN", syntax: "WHERE col BETWEEN a AND b;", desc: "Rango inclusivo [a, b].", example: "SELECT nombre, precio FROM productos WHERE precio BETWEEN 20 AND 60;", db: "tienda" },
  { cat: "Filtrado", cmd: "IS NULL", syntax: "WHERE col IS NULL;", desc: "Comprueba valores nulos (nunca uses = NULL).", example: "SELECT id, libro_id FROM prestamos WHERE fecha_devolucion IS NULL;", db: "biblioteca" },
  { cat: "Orden y límite", cmd: "ORDER BY", syntax: "ORDER BY col1 ASC, col2 DESC;", desc: "Ordena el resultado; ASC por defecto.", example: "SELECT nombre, salario FROM empleados ORDER BY salario DESC;", db: "empleados" },
  { cat: "Orden y límite", cmd: "LIMIT / OFFSET", syntax: "SELECT ... LIMIT n OFFSET m;", desc: "Paginación: n filas saltando las m primeras.", example: "SELECT nombre, precio FROM productos ORDER BY precio DESC LIMIT 3 OFFSET 2;", db: "tienda" },
  { cat: "Agregación", cmd: "COUNT", syntax: "SELECT COUNT(*) FROM tabla;", desc: "Número de filas (COUNT(col) ignora NULL).", example: "SELECT COUNT(*) AS pedidos FROM pedidos;", db: "tienda" },
  { cat: "Agregación", cmd: "SUM / AVG", syntax: "SELECT SUM(col), AVG(col) FROM tabla;", desc: "Suma y media de valores numéricos.", example: "SELECT ROUND(AVG(precio), 2) AS precio_medio FROM productos;", db: "tienda" },
  { cat: "Agregación", cmd: "MIN / MAX", syntax: "SELECT MIN(col), MAX(col) FROM tabla;", desc: "Valor mínimo y máximo (también con texto y fechas).", example: "SELECT MIN(salario), MAX(salario) FROM empleados;", db: "empleados" },
  { cat: "Agregación", cmd: "GROUP BY", syntax: "SELECT col, COUNT(*) FROM tabla GROUP BY col;", desc: "Calcula agregados por grupo de valores.", example: "SELECT cliente_id, COUNT(*) AS pedidos FROM pedidos GROUP BY cliente_id;", db: "tienda" },
  { cat: "Agregación", cmd: "HAVING", syntax: "GROUP BY col HAVING COUNT(*) > n;", desc: "Filtra grupos por agregados (WHERE no puede).", example: "SELECT cliente_id, COUNT(*) AS c FROM pedidos GROUP BY cliente_id HAVING COUNT(*) >= 2;", db: "tienda" },
  { cat: "JOIN", cmd: "INNER JOIN", syntax: "FROM a JOIN b ON a.id = b.a_id;", desc: "Filas con coincidencia en ambas tablas.", example: "SELECT p.id, c.nombre FROM pedidos p JOIN clientes c ON c.id = p.cliente_id;", db: "tienda" },
  { cat: "JOIN", cmd: "LEFT JOIN", syntax: "FROM a LEFT JOIN b ON a.id = b.a_id;", desc: "Todo el lado izquierdo; NULL donde no hay coincidencia.", example: "SELECT e.nombre, a.horas FROM empleados e LEFT JOIN asignaciones a ON a.empleado_id = e.id;", db: "empleados" },
  { cat: "JOIN", cmd: "RIGHT JOIN", syntax: "FROM a RIGHT JOIN b ON a.id = b.a_id;", desc: "Todo el lado derecho; NULL donde no hay coincidencia.", example: "SELECT e.nombre, a.proyecto_id FROM asignaciones a RIGHT JOIN empleados e ON e.id = a.empleado_id;", db: "empleados" },
  { cat: "JOIN", cmd: "Tabla derivada", syntax: "FROM (SELECT ...) AS d JOIN t ON ...;", desc: "JOIN contra el resultado de otra consulta (requiere alias).", example: "SELECT d.dep, d.media FROM (SELECT departamento_id AS dep, ROUND(AVG(salario), 2) AS media FROM empleados GROUP BY departamento_id) d ORDER BY d.media DESC;", db: "empleados" },
  { cat: "Subconsultas", cmd: "Subconsulta escalar", syntax: "WHERE col > (SELECT AVG(col) FROM tabla);", desc: "Una subconsulta que devuelve un único valor.", example: "SELECT nombre, precio FROM productos WHERE precio > (SELECT AVG(precio) FROM productos);", db: "tienda" },
  { cat: "Subconsultas", cmd: "IN (SELECT ...)", syntax: "WHERE col IN (SELECT col2 FROM tabla2);", desc: "Compara contra el conjunto devuelto por la subconsulta.", example: "SELECT nombre FROM clientes WHERE id IN (SELECT cliente_id FROM pedidos WHERE estado = 'pendiente');", db: "tienda" },
  { cat: "Subconsultas", cmd: "WITH (CTE)", syntax: "WITH t AS (SELECT ...) SELECT * FROM t;", desc: "Consulta con nombre, reutilizable y más legible.", example: "WITH t AS (SELECT cliente_id, COUNT(*) AS n FROM pedidos GROUP BY cliente_id) SELECT * FROM t WHERE n > 1;", db: "tienda" },
  { cat: "Subconsultas", cmd: "UNION", syntax: "SELECT ... UNION SELECT ...;", desc: "Une resultados eliminando duplicados (UNION ALL los conserva).", example: "SELECT nombre FROM empleados WHERE departamento_id = 1 UNION SELECT nombre FROM empleados WHERE departamento_id = 2;", db: "empleados" },
  { cat: "Expresiones", cmd: "CASE", syntax: "CASE WHEN cond THEN v1 ELSE v2 END", desc: "Valor condicional dentro de cualquier expresión.", example: "SELECT nombre, CASE WHEN precio > 100 THEN 'caro' ELSE 'barato' END AS tipo FROM productos;", db: "tienda" },
  { cat: "Expresiones", cmd: "Funciones de texto", syntax: "UPPER() LOWER() LENGTH() SUBSTR() TRIM() REPLACE() ||", desc: "Manipulación de cadenas; || concatena.", example: "SELECT UPPER(nombre) AS mayus, LENGTH(nombre) AS largo, SUBSTR(nombre, 1, 3) AS prefijo FROM clientes LIMIT 5;", db: "tienda" },
  { cat: "Expresiones", cmd: "COALESCE / ROUND / CAST", syntax: "COALESCE(a, b)  ROUND(x, n)  CAST(x AS INTEGER)", desc: "Primer valor no nulo, redondeo y conversión de tipo.", example: "SELECT titulo, COALESCE(genero, 'sin clasificar') AS genero, CAST(anio AS TEXT) AS anio_texto FROM libros;", db: "biblioteca" },
  { cat: "DML", cmd: "INSERT", syntax: "INSERT INTO tabla (c1, c2) VALUES (v1, v2);", desc: "Inserta una o varias filas: VALUES (..), (..).", example: "INSERT INTO productos (id, nombre, categoria, precio, stock) VALUES (11, 'Lámpara LED', 'Hogar', 15.5, 40); SELECT * FROM productos WHERE id = 11;", db: "tienda" },
  { cat: "DML", cmd: "UPDATE", syntax: "UPDATE tabla SET col = expr WHERE cond;", desc: "Modifica filas. ¡Siempre con WHERE!", example: "UPDATE productos SET stock = stock - 1 WHERE id = 2; SELECT id, nombre, stock FROM productos WHERE id = 2;", db: "tienda" },
  { cat: "DML", cmd: "DELETE", syntax: "DELETE FROM tabla WHERE cond;", desc: "Borra filas. Sin WHERE borra la tabla entera.", example: "DELETE FROM prestamos WHERE id = 1; SELECT COUNT(*) AS prestamos FROM prestamos;", db: "biblioteca" },
  { cat: "DDL", cmd: "CREATE TABLE", syntax: "CREATE TABLE t (id INTEGER PRIMARY KEY AUTOINCREMENT, col TEXT NOT NULL);", desc: "Crea tablas con tipos y restricciones. También CREATE TABLE t AS SELECT ...", example: "CREATE TABLE notas (id INTEGER PRIMARY KEY AUTOINCREMENT, texto TEXT NOT NULL, estado TEXT DEFAULT 'nueva'); INSERT INTO notas (texto) VALUES ('mi nota'); SELECT * FROM notas;", db: "tienda" },
  { cat: "DDL", cmd: "DROP TABLE", syntax: "DROP TABLE [IF EXISTS] tabla;", desc: "Elimina una tabla y todos sus datos.", example: "CREATE TABLE temporal (a INTEGER); DROP TABLE IF EXISTS temporal;", db: "tienda" },
  { cat: "Transacciones", cmd: "BEGIN / COMMIT / ROLLBACK", syntax: "BEGIN; ...cambios...; COMMIT; -- o ROLLBACK;", desc: "Agrupa cambios: todos o ninguno (atomicidad ACID).", example: "BEGIN; UPDATE productos SET precio = 0; ROLLBACK; SELECT COUNT(*) AS ceros FROM productos WHERE precio = 0;", db: "tienda" }
];

const DOCS_SECTIONS = [
  {
    title: "1 · Descripción general y arquitectura",
    blocks: [
      { k: "p", text: "SQLab es una plataforma educativa para aprender SQL desde el navegador. Esta entrega es un único archivo App.jsx autocontenido (motor + contenido + UI) para poder ejecutarse en cualquier entorno React. En un despliegue real se divide en los módulos que se describen a continuación." },
      { k: "list", items: [
        "Frontend: React/Next.js (App Router). Vistas: Inicio, Lecciones, Referencia, Desafíos, Editor, Tests y Docs. Routing por hash y progreso persistido en localStorage.",
        "Motor SQL del sandbox (lib/engine.js): tokenizer + parser + ejecutor en memoria con lista blanca de sentencias, límites de seguridad y errores didácticos. Es 100% local: nada sale del navegador.",
        "Backend opcional (server/index.js): API Node/Express + better-sqlite3 con el MISMO contrato que executeScript() — { ok, results, messages, error, ms } — para dar el salto a SQLite/PostgreSQL reales sin tocar la UI.",
        "Tests: suite integrada (vista Tests) + ejemplos de vitest (frontend) y node:test + supertest (backend)."
      ] },
      { k: "note", text: "Contrato único: si cambias runSql() del frontend por un fetch('POST /api/run'), la aplicación sigue funcionando igual. El servidor de referencia está abajo." }
    ]
  },
  {
    title: "2 · Estructura del proyecto",
    blocks: [
      { k: "code", lang: "text", code: String.raw`sqlab/
├── app/                      # Next.js (App Router)
│   ├── layout.jsx            # Fuentes Fontsource (Inter + JetBrains Mono), metadatos
│   ├── page.jsx              # Monta <App/> (este archivo, dividido en componentes)
│   └── globals.css           # La constante CSS de este archivo
├── components/
│   ├── SqlEditor.jsx         # Editor con resaltado, gutter y Ctrl+Enter
│   ├── DataTable.jsx         # Tabla de resultados (NULL, numeración, scroll)
│   ├── ExerciseCard.jsx      # Ejercicios y desafíos con validación por tests
│   └── views/                # Home, Lessons, Cheatsheet, Challenges, Playground, Tests, Docs
├── lib/
│   ├── engine.js             # Motor SQL del sandbox (sección ENGINE de este archivo)
│   ├── suite.js              # runTestSuite() (sección SUITE de este archivo)
│   └── content/              # lessons.js · challenges.js · cheatsheet.js · docs.js
├── server/
│   ├── index.js              # API Express segura (abajo)
│   ├── seeds.js              # Seeds con sentencias PREPARADAS (parámetros vinculados)
│   └── tests/api.test.js     # node:test + supertest
├── package.json
├── vitest.config.js
├── Dockerfile
└── README.md` }
    ]
  },
  {
    title: "3 · Instalación y scripts",
    blocks: [
      { k: "code", lang: "json", code: String.raw`{
  "name": "sqlab",
  "version": "1.0.0",
  "private": true,
  "scripts": {
    "dev": "next dev",
    "build": "next build",
    "start": "next start",
    "server": "node server/index.js",
    "test": "vitest run",
    "test:server": "node --test server/tests/",
    "lint": "eslint ."
  },
  "dependencies": {
    "next": "^15.0.0",
    "react": "^18.3.0",
    "react-dom": "^18.3.0",
    "framer-motion": "^11.0.0"
  },
  "devDependencies": {
    "vitest": "^2.0.0",
    "jsdom": "^24.0.0",
    "@testing-library/react": "^16.0.0",
    "eslint": "^9.0.0"
  },
  "serverDependenciesNote": "express ^4.19 · better-sqlite3 ^11 · helmet ^7 · cors ^2.8 · express-rate-limit ^7"
}` },
      { k: "code", lang: "bash", code: String.raw`# 1. Instalar dependencias
npm install
npm install express better-sqlite3 helmet cors express-rate-limit   # backend

# 2. Desarrollo (frontend en :3000, API en :4000)
npm run dev        # terminal 1
npm run server     # terminal 2

# 3. Tests y build de producción
npm test           # vitest (motor + componentes)
npm run test:server
npm run build && npm start` }
    ]
  },
  {
    title: "4 · Backend seguro (Node/Express + SQLite)",
    blocks: [
      { k: "p", text: "API de referencia que replica el contrato del sandbox con SQLite real. Defensas: lista blanca de sentencias, lista negra de keywords, límites de tamaño/filas, rate-limiting, helmet, CORS acotado, bases de datos EN MEMORIA por sesión (aisladas y descartables) y seeds con sentencias preparadas (nunca se concatena input del usuario)." },
      { k: "code", lang: "javascript", code: String.raw`// server/index.js — API segura para ejecutar SQL educativo
import express from 'express';
import helmet from 'helmet';
import cors from 'cors';
import rateLimit from 'express-rate-limit';
import Database from 'better-sqlite3';
import { seedAll } from './seeds.js';   // CREATE TABLE + INSERT con stmt.run(params)

const app = express();
app.use(helmet());
app.use(cors({ origin: process.env.CORS_ORIGIN || 'http://localhost:3000' }));
app.use(express.json({ limit: '64kb' }));            // cuerpo pequeño = menos abuso

const ALLOWED_START = new Set(['SELECT','WITH','INSERT','UPDATE','DELETE',
                               'CREATE','DROP','BEGIN','COMMIT','ROLLBACK']);
const FORBIDDEN_RE = /\b(ATTACH|DETACH|PRAGMA|VACUUM|REINDEX|LOAD_EXTENSION|COPY|ALTER|TRUNCATE)\b/i;
const MAX_LENGTH = 20000;
const MAX_ROWS = 1000;
const MAX_MS = 2000;

// Una BD en memoria por sesión anónima: aislada, caduca y jamás toca disco.
const sessions = new Map();
setInterval(() => {                                   // limpieza de sesiones viejas
  const t = Date.now();
  for (const [id, s] of sessions) if (t - s.createdAt > 30 * 60 * 1000) { s.db.close(); sessions.delete(id); }
}, 5 * 60 * 1000).unref();

function getDb(sessionId) {
  if (!sessions.has(sessionId)) {
    const db = new Database(':memory:');
    seedAll(db);                                      // parámetros vinculados (anti-inyección)
    sessions.set(sessionId, { db, createdAt: Date.now() });
  }
  return sessions.get(sessionId).db;
}

function assertSafe(sql) {
  if (typeof sql !== 'string' || !sql.trim()) return fail(400, 'SQL vacío');
  if (sql.length > MAX_LENGTH) return fail(413, 'SQL demasiado largo');
  if (FORBIDDEN_RE.test(sql)) return fail(400, 'Instrucción no permitida en el entorno educativo');
  const first = sql.trim().split(/[\s(]+/)[0].toUpperCase();
  if (!ALLOWED_START.has(first)) return fail(400, 'Sentencia fuera de la lista blanca');
}
function fail(status, message) { const e = new Error(message); e.status = status; throw e; }

app.get('/api/health', (req, res) => res.json({ ok: true }));

app.post('/api/run',
  rateLimit({ windowMs: 60 * 1000, max: 60, standardHeaders: true }),
  (req, res) => {
    const t0 = Date.now();
    try {
      const { sql } = req.body || {};
      const sessionId = String((req.body && req.body.sessionId) || 'anon').slice(0, 64);
      assertSafe(sql);
      const db = getDb(sessionId);
      const stmt = db.prepare(sql);                   // better-sqlite3 valida la sintaxis
      let results = []; let messages = [];
      if (stmt.reader) {
        const rows = stmt.raw().all().slice(0, MAX_ROWS);
        results.push({ kind: 'rows', columns: stmt.columns().map(c => c.name), rows, rowCount: rows.length });
      } else {
        const info = stmt.run();
        messages.push({ type: 'success', text: info.changes + ' fila(s) afectada(s).' });
      }
      if (Date.now() - t0 > MAX_MS) fail(408, 'Consulta demasiado lenta');
      res.json({ ok: true, results, messages, error: null, ms: Date.now() - t0 });
    } catch (err) {
      res.status(err.status || 400).json({ ok: false, results: [], messages: [],
        error: { message: err.message, hint: null }, ms: Date.now() - t0 });
    }
  });

app.post('/api/reset', (req, res) => {                // restaura la BD de la sesión
  const sessionId = String((req.body && req.body.sessionId) || 'anon').slice(0, 64);
  const s = sessions.get(sessionId);
  if (s) { s.db.close(); sessions.delete(sessionId); }
  res.json({ ok: true });
});

const port = process.env.PORT || 4000;
app.listen(port, () => console.log('SQLab API en :' + port));
export default app;` },
      { k: "p", text: "Integración frontend: sustituye la llamada local por la API manteniendo el mismo contrato." },
      { k: "code", lang: "javascript", code: String.raw`// lib/api.js — mismo contrato que executeScript(db, sql)
export async function runSql(dbKey, sql, sessionId) {
  const res = await fetch('/api/run', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ sql, sessionId: sessionId + ':' + dbKey })
  });
  if (!res.ok && res.status >= 500) throw new Error('El servidor no responde');
  return res.json(); // { ok, results, messages, error, ms }
}` }
    ]
  },
  {
    title: "5 · Tests (frontend y backend)",
    blocks: [
      { k: "p", text: "La vista “Tests” de esta app ejecuta runTestSuite(): más de 60 pruebas reales sobre el motor (seguridad, ejecución, errores y contrato de UX). En CI, las mismas pruebas viven en vitest, y la API se cubre con node:test + supertest." },
      { k: "code", lang: "javascript", code: String.raw`// lib/engine.test.js (vitest)
import { describe, it, expect } from 'vitest';
import { executeScript, freshDb } from './engine';

describe('Motor SQL', () => {
  it('ejecuta un SELECT básico', () => {
    const out = executeScript(freshDb('tienda'), 'SELECT COUNT(*) FROM clientes;');
    expect(out.ok).toBe(true);
    expect(out.results[0].rows[0][0]).toBe(8);
  });
  it('bloquea PRAGMA y otras keywords peligrosas', () => {
    expect(executeScript(freshDb('tienda'), 'PRAGMA table_info(clientes);').ok).toBe(false);
    expect(executeScript(freshDb('tienda'), 'ATTACH DATABASE "x" AS y;').ok).toBe(false);
  });
  it('trata el SQL dentro de literales como dato (anti-inyección)', () => {
    const db = freshDb('tienda');
    executeScript(db, "SELECT * FROM clientes WHERE nombre = 'x''; DROP TABLE clientes; --';");
    expect(Object.keys(db.tables)).toContain('clientes');
    expect(db.tables.clientes.rows).toHaveLength(8);
  });
  it('devuelve errores didácticos con pista', () => {
    const out = executeScript(freshDb('tienda'), 'SELECT * FROM usuarios;');
    expect(out.ok).toBe(false);
    expect(out.error.message).toMatch(/No existe la tabla/);
    expect(out.error.hint).toMatch(/productos/);
  });
  it('JOIN + GROUP BY correctos', () => {
    const out = executeScript(freshDb('tienda'),
      'SELECT c.nombre, COUNT(p.id) FROM clientes c LEFT JOIN pedidos p ON p.cliente_id = c.id GROUP BY c.nombre HAVING COUNT(p.id) = 3;');
    expect(out.results[0].rows).toEqual([['Ana García', 3]]);
  });
  it('ROLLBACK deshace los cambios', () => {
    const db = freshDb('tienda');
    executeScript(db, 'BEGIN; DELETE FROM clientes; ROLLBACK;');
    expect(db.tables.clientes.rows).toHaveLength(8);
  });
});` },
      { k: "code", lang: "javascript", code: String.raw`// server/tests/api.test.js (node:test + supertest)
import test from 'node:test';
import assert from 'node:assert';
import request from 'supertest';
import app from '../index.js';

test('POST /api/run devuelve filas para un SELECT válido', async () => {
  const res = await request(app).post('/api/run')
    .send({ sql: 'SELECT 1 AS uno;', sessionId: 't1' });
  assert.equal(res.status, 200);
  assert.equal(res.body.ok, true);
  assert.equal(res.body.results[0].rows[0][0], 1);
});

test('POST /api/run rechaza sentencias fuera de la lista blanca', async () => {
  const res = await request(app).post('/api/run')
    .send({ sql: 'PRAGMA table_info(x);', sessionId: 't2' });
  assert.equal(res.status, 400);
  assert.equal(res.body.ok, false);
});

test('POST /api/run devuelve error 400 con SQL vacío', async () => {
  const res = await request(app).post('/api/run').send({ sql: '  ', sessionId: 't3' });
  assert.equal(res.status, 400);
});

test('GET /api/health responde ok', async () => {
  const res = await request(app).get('/api/health');
  assert.equal(res.body.ok, true);
});` }
    ]
  },
  {
    title: "6 · Cómo añadir una lección nueva",
    blocks: [
      { k: "p", text: "Añade un objeto al array LESSONS (lib/content/lessons.js). La UI, el routing (#/lecciones/TU-ID) y el progreso se actualizan solos." },
      { k: "code", lang: "javascript", code: String.raw`{
  id: 'basico-6',              // único; define la ruta #/lecciones/basico-6
  level: 'Básico',             // 'Básico' | 'Intermedio' | 'Avanzado'
  title: 'Título de la lección',
  subtitle: 'Resumen de una línea',
  minutes: 8,
  blocks: [                    // teoría + ejemplos VISUALES ejecutables
    { k: 'p',    text: 'Párrafo; el texto entre comillas invertidas se ve como código.' },
    { k: 'list', items: ['punto 1', 'punto 2'] },
    { k: 'note', text: 'Consejo destacado.' },
    { k: 'sql',  db: 'tienda', sql: 'SELECT 1;', caption: 'Ejemplo en vivo',
      preview: 'SELECT * FROM t;' /* opcional: resultado a mostrar tras DML */ }
  ],
  exercise: {
    db: 'tienda',
    prompt: 'Enunciado del ejercicio práctico.',
    initialSql: '-- punto de partida\n',
    hint: 'Pista opcional.',
    solution: 'SELECT ...;',
    tests: [
      { label: 'Devuelve N filas', check: (ctx) => (lastRows(ctx.out) || []).length === N },
      { label: 'Estado final de la BD', check: (ctx) => ctx.db.tables.t.rows.length === M }
    ]
  }
}` },
      { k: "p", text: "Para añadir una BASE DE DATOS de ejemplo: crea una función seed en DB_SEEDS (makeTable ayuda a definirla), añade su clave a DB_KEYS y su ficha a DB_INFO. Para añadir tests a la suite: usa test(grupo, nombre, fn) dentro de runTestSuite()." }
    ]
  },
  {
    title: "7 · Seguridad del sandbox",
    blocks: [
      { k: "list", items: [
        "Lista blanca de sentencias (SELECT, WITH, INSERT, UPDATE, DELETE, CREATE, DROP, BEGIN/COMMIT/ROLLBACK): todo lo demás se rechaza antes de parsear.",
        "Lista negra de keywords de administración de SGBD (PRAGMA, ATTACH, ALTER, VACUUM, LOAD_EXTENSION, SLEEP…).",
        "Tokenizador propio: el punto y coma dentro de literales NO separa sentencias, así que el SQL embebido en strings se trata como DATO (probado en la suite anti-inyección).",
        "Límites: 20 000 caracteres, 25 sentencias, 1 000 filas de resultado y 250 000 combinaciones de JOIN (anti denegación de servicio).",
        "Datos en memoria, reiniciables (Reiniciar BD). El motor nunca accede a red ni disco.",
        "El resaltado del editor escapa HTML (anti-XSS). En el backend: seeds con parámetros vinculados, helmet, CORS, rate-limit y sesiones de BD aisladas con caducidad."
      ] }
    ]
  },
  {
    title: "8 · Despliegue",
    blocks: [
      { k: "list", items: [
        "Frontend (Next.js): Vercel — vercel --prod o push al repo conectado. Build estático, sin variables obligatorias.",
        "Backend (Express): Render/Fly/Railway — variable PORT y CORS_ORIGIN con el dominio del frontend.",
        "Docker: imagen única con next start (ver Dockerfile abajo).",
        "Modo 100% cliente: la app YA funciona sin backend (motor en el navegador); puedes publicar solo el frontend en cualquier hosting estático.",
        "Variables: CORS_ORIGIN, PORT. En producción añade analítica y monitorización de errores (p. ej. Sentry)."
      ] },
      { k: "code", lang: "dockerfile", code: String.raw`FROM node:20-alpine
WORKDIR /app
COPY package*.json ./
RUN npm ci --omit=dev
COPY . .
RUN npm run build
EXPOSE 3000
ENV NODE_ENV=production
CMD ["npm", "start"]` }
    ]
  },
  {
    title: "9 · Limitaciones conocidas del motor sandbox",
    blocks: [
      { k: "list", items: [
        "Sin subconsultas correlacionadas (usa JOIN o tablas derivadas).",
        "Sin funciones de ventana (ROW_NUMBER, RANK…) ni ALTER TABLE.",
        "HAVING no acepta alias de salida (usa la expresión agregada completa).",
        "Una sola base de datos por consulta (no hay JOIN entre tienda y empleados).",
        "LIKE no admite cláusula ESCAPE; las fechas son texto ISO (comparables lexicográficamente)."
      ] }
    ]
  }
];

/* ============================================================================
 * UI — Contexto, routing y utilidades
 * ========================================================================== */

const AppCtx = createContext(null);
const useApp = () => useContext(AppCtx);

function loadProgress() {
  try {
    const raw = window.localStorage.getItem("sqlab:progress");
    if (raw) {
      const p = JSON.parse(raw);
      return { lessons: p.lessons || {}, challenges: p.challenges || {} };
    }
  } catch (e) { /* almacenamiento no disponible */ }
  return { lessons: {}, challenges: {} };
}

function useRoute() {
  const parse = () => (typeof window === "undefined" ? [] : (window.location.hash || "#/").replace(/^#\/?/, "").split("/").filter(Boolean));
  const [parts, setParts] = useState(parse);
  useEffect(() => {
    const fn = () => { setParts(parse()); window.scrollTo({ top: 0 }); };
    window.addEventListener("hashchange", fn);
    return () => window.removeEventListener("hashchange", fn);
  }, []);
  return parts;
}
function navigate(path) { window.location.hash = "#/" + String(path || "").replace(/^\//, ""); }

function injectFonts() {
  if (typeof document === "undefined") return;
  const links = [
    ["fs-inter-400", "https://cdn.jsdelivr.net/npm/@fontsource/inter@5.0.18/index.css"],
    ["fs-inter-500", "https://cdn.jsdelivr.net/npm/@fontsource/inter@5.0.18/500.css"],
    ["fs-inter-600", "https://cdn.jsdelivr.net/npm/@fontsource/inter@5.0.18/600.css"],
    ["fs-inter-700", "https://cdn.jsdelivr.net/npm/@fontsource/inter@5.0.18/700.css"],
    ["fs-mono-400", "https://cdn.jsdelivr.net/npm/@fontsource/jetbrains-mono@5.0.20/index.css"],
    ["fs-mono-700", "https://cdn.jsdelivr.net/npm/@fontsource/jetbrains-mono@5.0.20/700.css"]
  ];
  links.forEach((pair) => {
    if (document.getElementById(pair[0])) return;
    const l = document.createElement("link");
    l.id = pair[0]; l.rel = "stylesheet"; l.href = pair[1];
    document.head.appendChild(l);
  });
}

function summarize(out) {
  if (!out.ok && out.error) return out.error.message;
  const rows = out.results.find((r) => r.kind === "rows");
  if (rows) return rows.rowCount + " fila(s)";
  if (out.messages.length) return out.messages[0].text;
  return "OK";
}
function fmtTime(d) {
  try { return new Date(d).toLocaleTimeString("es-ES", { hour: "2-digit", minute: "2-digit", second: "2-digit" }); }
  catch (e) { return ""; }
}
function fmtVal(v) {
  if (v === null || v === undefined) return "NULL";
  return String(v);
}

/* ---------- Primitivas de UI ---------- */

function Btn({ children, onClick, variant = "primary", className = "", title, disabled }) {
  return (
    <button type="button" title={title} disabled={disabled} onClick={onClick}
      className={"btn btn-" + variant + (className ? " " + className : "")}>
      {children}
    </button>
  );
}

function Badge({ children, tone = "neutral" }) {
  return <span className={"badge badge-" + tone}>{children}</span>;
}

function levelTone(level) {
  return level === "Básico" ? "basico" : level === "Intermedio" ? "intermedio" : "avanzado";
}

function CopyButton({ text, label = "Copiar" }) {
  const [ok, setOk] = useState(false);
  const copy = () => {
    try {
      if (navigator.clipboard && navigator.clipboard.writeText) {
        navigator.clipboard.writeText(text).then(() => { setOk(true); setTimeout(() => setOk(false), 1400); });
      } else {
        const ta = document.createElement("textarea");
        ta.value = text; document.body.appendChild(ta); ta.select();
        document.execCommand("copy"); document.body.removeChild(ta);
        setOk(true); setTimeout(() => setOk(false), 1400);
      }
    } catch (e) { /* clipboard no disponible */ }
  };
  return <button type="button" className="btn-mini" onClick={copy}>{ok ? "✓ Copiado" : label}</button>;
}

function CodeBlock({ sql, lang = "sql" }) {
  const html = lang === "sql" ? highlightSql(sql) : esc(sql);
  return (
    <div className="codeblock">
      <div className="codeblock-bar">
        <span className="codeblock-lang">{lang}</span>
        <CopyButton text={sql} />
      </div>
      <pre className="codeblock-pre" dangerouslySetInnerHTML={{ __html: html }} />
    </div>
  );
}

function DataTable({ columns, rows, maxRows = 100 }) {
  const shown = rows.slice(0, maxRows);
  return (
    <div className="table-wrap">
      <table className="data-table">
        <thead>
          <tr><th className="rownum">#</th>{columns.map((c, i) => <th key={i}>{String(c)}</th>)}</tr>
        </thead>
        <tbody>
          {shown.length === 0 && (
            <tr><td className="empty-cell" colSpan={columns.length + 1}>0 filas — consulta correcta, resultado vacío.</td></tr>
          )}
          {shown.map((r, ri) => (
            <tr key={ri}>
              <td className="rownum">{ri + 1}</td>
              {columns.map((c, ci) => {
                const v = r[ci];
                if (v === null || v === undefined) return <td key={ci}><span className="cell-null">NULL</span></td>;
                if (typeof v === "number") return <td key={ci} className="cell-num">{String(v)}</td>;
                return <td key={ci}>{String(v)}</td>;
              })}
            </tr>
          ))}
        </tbody>
      </table>
      {rows.length > shown.length && <div className="table-more">Mostrando {shown.length} de {rows.length} filas.</div>}
    </div>
  );
}

function ErrorBanner({ error }) {
  if (!error) return null;
  return (
    <div className="msg msg-error" role="alert">
      <div className="msg-title"><span className="msg-icon">✕</span>{error.message}</div>
      {error.hint && <div className="msg-hint">💡 {error.hint}</div>}
    </div>
  );
}

function MessageList({ messages }) {
  if (!messages || !messages.length) return <div className="muted small">Sin mensajes.</div>;
  return (
    <div className="msg-list">
      {messages.map((m, i) => (
        <div key={i} className={"msg msg-" + m.type}>
          <span className="msg-icon">{m.type === "success" ? "✓" : m.type === "warning" ? "⚠" : "✕"}</span>
          <span>{m.text}</span>
        </div>
      ))}
    </div>
  );
}

function inlineFmt(text) {
  const parts = String(text).split("`");
  return parts.map((p, i) =>
    i % 2 === 1 ? <code key={i} className="inline-code">{p}</code> : <React.Fragment key={i}>{p}</React.Fragment>
  );
}

/* ---------- Editor SQL con resaltado ---------- */

function SqlEditor({ value, onChange, onRun, height = 200, editorId }) {
  const taRef = useRef(null);
  const preRef = useRef(null);
  const gutRef = useRef(null);
  const lineCount = value.split("\n").length;

  const sync = () => {
    const ta = taRef.current;
    if (!ta) return;
    if (preRef.current) { preRef.current.scrollTop = ta.scrollTop; preRef.current.scrollLeft = ta.scrollLeft; }
    if (gutRef.current) { gutRef.current.scrollTop = ta.scrollTop; }
  };

  const onKeyDown = (e) => {
    if ((e.metaKey || e.ctrlKey) && e.key === "Enter") { e.preventDefault(); if (onRun) onRun(); return; }
    if (e.key === "Tab") {
      e.preventDefault();
      const ta = taRef.current;
      const s = ta.selectionStart; const en = ta.selectionEnd;
      onChange(value.slice(0, s) + "  " + value.slice(en));
      requestAnimationFrame(() => { ta.selectionStart = ta.selectionEnd = s + 2; });
    }
  };

  return (
    <div className="sqleditor">
      <div className="sqleditor-inner">
        <div className="editor-gutter" ref={gutRef} aria-hidden="true">
          {Array.from({ length: lineCount }, (x, i) => <div key={i}>{i + 1}</div>)}
        </div>
        <div className="editor-area" style={{ height: height + "px" }}>
          <pre ref={preRef} className="editor-highlight" aria-hidden="true"
            dangerouslySetInnerHTML={{ __html: highlightSql(value) + "\n" }} />
          <textarea
            id={editorId}
            ref={taRef}
            value={value}
            onChange={(e) => onChange(e.target.value)}
            onScroll={sync}
            onKeyDown={onKeyDown}
            spellCheck={false}
            autoCapitalize="off"
            autoCorrect="off"
            aria-label="Editor de consultas SQL"
            placeholder="Escribe tu consulta SQL aquí…"
          />
        </div>
      </div>
    </div>
  );
}

/* ---------- Ejemplos en vivo ---------- */

function LiveExample({ sql, db = "tienda", preview, caption }) {
  const data = useMemo(() => {
    const clone = freshDb(db);
    const main = executeScript(clone, sql);
    const prev = preview && main.ok ? executeScript(clone, preview) : null;
    return { main, prev };
  }, [sql, db, preview]);
  const show = data.prev && data.prev.results.length ? data.prev : data.main;
  const rowsRes = show.results.filter((r) => r.kind === "rows");
  return (
    <div className="live-example">
      <CodeBlock sql={preview ? sql + "\n\n" + preview : sql} />
      {rowsRes.length > 0 && (
        <div className="live-result">
          <div className="result-meta small muted">Resultado {preview ? "de la comprobación" : ""} · {rowsRes[rowsRes.length - 1].rowCount} filas</div>
          <DataTable columns={rowsRes[rowsRes.length - 1].columns} rows={rowsRes[rowsRes.length - 1].rows} maxRows={8} />
        </div>
      )}
      {rowsRes.length === 0 && show.messages.length > 0 && <MessageList messages={show.messages} />}
      {show.error && <ErrorBanner error={show.error} />}
      {caption && <div className="example-caption">{inlineFmt(caption)}</div>}
    </div>
  );
}

/* ---------- Tarjeta de ejercicio (lecciones y desafíos) ---------- */

function ExerciseCard({ dbKey, prompt, initialSql, hint, solution, tests, onPassed, completed }) {
  const [sql, setSql] = useState(initialSql || "");
  const [out, setOut] = useState(null);
  const [checks, setChecks] = useState(null);
  const [passed, setPassed] = useState(false);
  const [showHint, setShowHint] = useState(false);
  const [showSolution, setShowSolution] = useState(false);

  const run = () => {
    const clone = freshDb(dbKey);
    const res = executeScript(clone, sql);
    setOut(res);
    const ctx = { out: res, db: clone };
    const cs = tests.map((t) => {
      try { return { label: t.label, passed: !!t.check(ctx) }; }
      catch (e) { return { label: t.label, passed: false, error: String((e && e.message) || e) }; }
    });
    setChecks(cs);
    const allOk = res.ok && cs.every((c) => c.passed);
    setPassed(allOk);
    if (allOk && onPassed) onPassed();
  };

  const reset = () => { setSql(initialSql || ""); setOut(null); setChecks(null); setPassed(false); };

  const rowsResults = out ? out.results.filter((r) => r.kind === "rows") : [];

  return (
    <div className="exercise card">
      <div className="exercise-head">
        <h3>Ejercicio práctico</h3>
        {completed && <Badge tone="success">Completada</Badge>}
        {passed && !completed && <Badge tone="success">¡Superado!</Badge>}
      </div>
      <p className="exercise-prompt">{inlineFmt(prompt)}</p>
      <div className="exercise-db small muted">Base de datos: <strong>{DB_INFO[dbKey].emoji} {DB_INFO[dbKey].label}</strong> · se ejecuta sobre una copia limpia (puedes repetir sin miedo)</div>
      <SqlEditor value={sql} onChange={setSql} onRun={run} height={170} />
      <div className="exercise-actions">
        <Btn onClick={run}>▶ Ejecutar y comprobar</Btn>
        <Btn variant="ghost" onClick={reset}>Reiniciar</Btn>
        <Btn variant="ghost" onClick={() => setShowHint(!showHint)}>{showHint ? "Ocultar pista" : "Ver pista"}</Btn>
        <Btn variant="ghost" onClick={() => setShowSolution(!showSolution)}>{showSolution ? "Ocultar solución" : "Ver solución"}</Btn>
      </div>
      {showHint && hint && <div className="callout">💡 {inlineFmt(hint)}</div>}
      {showSolution && solution && <div className="solution"><div className="small muted mb-4">Solución propuesta:</div><CodeBlock sql={solution} /></div>}

      {out && (
        <div className="exercise-out">
          {out.error && <ErrorBanner error={out.error} />}
          {!out.error && out.messages.length > 0 && <MessageList messages={out.messages} />}
          {rowsResults.length > 0 && rowsResults.map((r, i) => (
            <div key={i} className="live-result">
              <div className="result-meta small muted">{r.rowCount} filas · {out.ms} ms</div>
              <DataTable columns={r.columns} rows={r.rows} maxRows={12} />
            </div>
          ))}
          {checks && (
            <ul className="tests-list">
              {checks.map((c, i) => (
                <li key={i} className={"test-item " + (c.passed ? "pass" : "fail")}>
                  <span className="test-icon">{c.passed ? "✓" : "✕"}</span>
                  <span>{c.label}</span>
                  {!c.passed && c.error && <span className="test-err">({c.error})</span>}
                </li>
              ))}
            </ul>
          )}
          {passed && <div className="msg msg-success" role="status"><span className="msg-icon">✓</span><span>Ejercicio superado. ¡Buen trabajo!</span></div>}
        </div>
      )}
    </div>
  );
}

/* ---------- Vistas ---------- */

function Home() {
  const { progress } = useApp();
  const doneL = Object.keys(progress.lessons).filter((k) => progress.lessons[k]).length;
  const doneC = Object.keys(progress.challenges).filter((k) => progress.challenges[k]).length;
  return (
    <div>
      <section className="hero">
        <motion.div initial={{ opacity: 0, y: 14 }} animate={{ opacity: 1, y: 0 }} transition={{ duration: 0.45 }}>
          <span className="hero-badge">Plataforma educativa · SQL interactivo</span>
          <h1 className="hero-title">Aprende SQL escribiendo consultas de verdad</h1>
          <p className="hero-sub">
            De tu primer <code className="inline-code">SELECT</code> a CTEs, JOINs y transacciones:
            {LESSONS.length} lecciones guiadas, {CHALLENGES.length} desafíos con validación automática y un editor
            con 3 bases de datos de ejemplo que se ejecutan al instante — con errores explicados, historial y tests integrados.
          </p>
          <div className="hero-cta">
            <Btn onClick={() => navigate("lecciones/" + LESSONS[0].id)}>Empezar la primera lección</Btn>
            <Btn variant="ghost" onClick={() => navigate("editor")}>Abrir el editor SQL</Btn>
          </div>
          <div className="hero-stats">
            <div className="stat"><strong>{LESSONS.length}</strong><span>lecciones</span></div>
            <div className="stat"><strong>{CHALLENGES.length}</strong><span>desafíos</span></div>
            <div className="stat"><strong>3</strong><span>bases de datos</span></div>
            <div className="stat"><strong>{doneL}/{LESSONS.length}</strong><span>completadas</span></div>
            <div className="stat"><strong>{doneC}/{CHALLENGES.length}</strong><span>desafíos</span></div>
          </div>
        </motion.div>
      </section>

      <section className="section">
        <h2 className="section-title">¿Qué es SQL?</h2>
        <p className="section-sub">
          SQL (Structured Query Language) es el lenguaje estándar para consultar y manipular bases de datos
          relacionales: datos organizados en tablas conectadas entre sí. Lo usan a diario desde hojas de cálculo
          hasta los mayores sistemas del mundo. Se aprende haciendo: prueba este ejemplo en vivo.
        </p>
        <LiveExample
          db="tienda"
          sql={"SELECT nombre, categoria, precio\nFROM productos\nWHERE precio < 50\nORDER BY precio DESC;"}
          caption="Productos de menos de 50 € ordenados por precio. Este mismo ejemplo se ejecuta en tu navegador con el motor del sandbox."
        />
      </section>

      <section className="section">
        <h2 className="section-title">Cómo funciona</h2>
        <div className="grid-4">
          {[
            { t: "1 · Aprende", d: "Teoría breve con ejemplos ejecutables que muestran el resultado real al instante." },
            { t: "2 · Practica", d: "Editor SQL integrado con resaltado, esquema de la BD, historial y Ctrl+Enter." },
            { t: "3 · Recibe feedback", d: "Errores traducidos a lenguaje humano con pistas accionables; avisos ante UPDATE/DELETE sin WHERE." },
            { t: "4 · Progresa", d: "Ejercicios y desafíos validados por tests automáticos; tu progreso se guarda en el navegador." }
          ].map((f, i) => (
            <motion.div key={i} className="card feature-card" initial={{ opacity: 0, y: 12 }} whileInView={{ opacity: 1, y: 0 }} viewport={{ once: true }} transition={{ delay: i * 0.06 }}>
              <h3>{f.t}</h3><p className="muted">{f.d}</p>
            </motion.div>
          ))}
        </div>
      </section>

      <section className="section">
        <h2 className="section-title">Ruta de aprendizaje</h2>
        <div className="grid-3">
          {LEVELS.map((lv) => {
            const lessons = LESSONS.filter((l) => l.level === lv);
            const done = lessons.filter((l) => progress.lessons[l.id]).length;
            return (
              <div key={lv} className="card level-card">
                <div className="level-head">
                  <Badge tone={levelTone(lv)}>{lv}</Badge>
                  <span className="muted small">{done}/{lessons.length}</span>
                </div>
                <div className="progress"><div className="progress-fill" style={{ width: (lessons.length ? (done / lessons.length) * 100 : 0) + "%" }} /></div>
                <ul className="level-list">
                  {lessons.map((l) => (
                    <li key={l.id}>
                      <a href={"#/lecciones/" + l.id}>
                        {progress.lessons[l.id] && <span className="tick">✓</span>} {l.title}
                      </a>
                    </li>
                  ))}
                </ul>
                <Btn variant="ghost" className="mt-8" onClick={() => navigate("lecciones/" + lessons[0].id)}>Ir al nivel</Btn>
              </div>
            );
          })}
        </div>
      </section>

      <section className="section">
        <div className="card note-card">
          <h3>Sandbox seguro por diseño</h3>
          <p className="muted">
            Las consultas se validan contra una lista blanca de sentencias y una lista negra de comandos de
            administración (PRAGMA, ATTACH, ALTER…) antes de ejecutarse sobre datos de ejemplo en memoria.
            El SQL dentro de literales de texto se trata siempre como dato. Nada toca tu sistema: puedes
            experimentar (y romper cosas) con total libertad, y restaurar con “Reiniciar BD”.
          </p>
        </div>
      </section>
    </div>
  );
}

function LessonsIndex() {
  const { progress } = useApp();
  return (
    <div className="page">
      <h1 className="page-title">Lecciones</h1>
      <p className="page-sub">Progresión guiada de básico a avanzado. Cada lección incluye teoría, ejemplos ejecutables y un ejercicio validado por tests.</p>
      {LEVELS.map((lv) => {
        const lessons = LESSONS.filter((l) => l.level === lv);
        const done = lessons.filter((l) => progress.lessons[l.id]).length;
        return (
          <section key={lv} className="section">
            <div className="section-head">
              <h2><Badge tone={levelTone(lv)}>{lv}</Badge></h2>
              <span className="muted small">{done} de {lessons.length} completadas</span>
            </div>
            <div className="lesson-list">
              {lessons.map((l, idx) => (
                <button key={l.id} type="button" className="lesson-row" onClick={() => navigate("lecciones/" + l.id)}>
                  <span className={"lesson-num" + (progress.lessons[l.id] ? " done" : "")}>
                    {progress.lessons[l.id] ? "✓" : LESSONS.indexOf(l) + 1}
                  </span>
                  <span className="lesson-info">
                    <span className="lesson-title">{l.title}</span>
                    <span className="lesson-sub">{l.subtitle}</span>
                  </span>
                  <span className="lesson-meta small muted">{l.minutes} min</span>
                </button>
              ))}
            </div>
          </section>
        );
      })}
    </div>
  );
}

function LessonBlocks({ blocks }) {
  return (
    <div>
      {blocks.map((b, i) => {
        if (b.k === "p") return <p key={i} className="lesson-p">{inlineFmt(b.text)}</p>;
        if (b.k === "note") return <div key={i} className="callout">💡 {inlineFmt(b.text)}</div>;
        if (b.k === "list") return <ul key={i} className="lesson-list">{b.items.map((it, j) => <li key={j}>{inlineFmt(it)}</li>)}</ul>;
        if (b.k === "sql") return <div key={i} className="example-block"><LiveExample sql={b.sql} db={b.db} preview={b.preview} caption={b.caption} /></div>;
        return null;
      })}
    </div>
  );
}

function LessonDetail({ id }) {
  const { progress, markDone } = useApp();
  const idx = LESSONS.findIndex((l) => l.id === id);
  if (idx === -1) return <div className="page"><h1 className="page-title">Lección no encontrada</h1><Btn variant="ghost" onClick={() => navigate("lecciones")}>Volver a lecciones</Btn></div>;
  const lesson = LESSONS[idx];
  const prev = idx > 0 ? LESSONS[idx - 1] : null;
  const next = idx < LESSONS.length - 1 ? LESSONS[idx + 1] : null;
  return (
    <div className="page lesson-page">
      <div className="lesson-head-bar">
        <a className="back-link" href="#/lecciones">← Todas las lecciones</a>
        <div>
          <Badge tone={levelTone(lesson.level)}>{lesson.level}</Badge>
          {progress.lessons[lesson.id] && <span className="ml-8"><Badge tone="success">Completada</Badge></span>}
        </div>
      </div>
      <h1 className="page-title">{lesson.title}</h1>
      <p className="page-sub">{lesson.subtitle} · {lesson.minutes} min</p>
      <div className="lesson-body">
        <LessonBlocks blocks={lesson.blocks} />
        <ExerciseCard
          dbKey={lesson.exercise.db}
          prompt={lesson.exercise.prompt}
          initialSql={lesson.exercise.initialSql}
          hint={lesson.exercise.hint}
          solution={lesson.exercise.solution}
          tests={lesson.exercise.tests}
          completed={!!progress.lessons[lesson.id]}
          onPassed={() => markDone("lessons", lesson.id)}
        />
        <div className="lesson-nav">
          {prev ? <Btn variant="ghost" onClick={() => navigate("lecciones/" + prev.id)}>← {prev.title}</Btn> : <span />}
          {next ? <Btn onClick={() => navigate("lecciones/" + next.id)}>{next.title} →</Btn> : <Btn onClick={() => navigate("desafios")}>Ir a desafíos 🏁</Btn>}
        </div>
      </div>
    </div>
  );
}

function CheatsheetView() {
  const { openInEditor } = useApp();
  const [q, setQ] = useState("");
  const query = q.trim().toLowerCase();
  const cats = [];
  CHEATSHEET.forEach((c) => { if (cats.indexOf(c.cat) === -1) cats.push(c.cat); });
  const filtered = CHEATSHEET.filter((c) =>
    !query || (c.cmd + " " + c.syntax + " " + c.desc + " " + c.example).toLowerCase().indexOf(query) !== -1);
  return (
    <div className="page">
      <h1 className="page-title">Referencia rápida</h1>
      <p className="page-sub">Los comandos SQL más usados, con sintaxis, descripción y un ejemplo que puedes enviar al editor con un clic.</p>
      <input className="search-input" type="search" value={q} onChange={(e) => setQ(e.target.value)}
        placeholder="Buscar comando… (ej: JOIN, LIKE, GROUP)" aria-label="Buscar en la referencia" />
      {cats.map((cat) => {
        const items = filtered.filter((c) => c.cat === cat);
        if (!items.length) return null;
        return (
          <section key={cat} className="section">
            <h2 className="section-title-sm">{cat}</h2>
            <div className="grid-2">
              {items.map((c, i) => (
                <div key={i} className="card cheat-card">
                  <div className="cheat-head">
                    <code className="cheat-cmd">{c.cmd}</code>
                    <span className="muted small">{DB_INFO[c.db].emoji} {DB_INFO[c.db].label}</span>
                  </div>
                  <div className="cheat-syntax"><code>{c.syntax}</code></div>
                  <p className="muted small">{c.desc}</p>
                  <CodeBlock sql={c.example} />
                  <div className="cheat-actions">
                    <Btn variant="ghost" onClick={() => openInEditor(c.example, c.db)}>Probar en el editor →</Btn>
                  </div>
                </div>
              ))}
            </div>
          </section>
        );
      })}
      {filtered.length === 0 && <div className="empty-state">Sin resultados para “{q}”.</div>}
    </div>
  );
}

function ChallengesIndex() {
  const { progress } = useApp();
  return (
    <div className="page">
      <h1 className="page-title">Desafíos</h1>
      <p className="page-sub">Ejercicios acumulativos que combinan varios conceptos. Cada desafío se valida con tests automáticos sobre una copia limpia de la base de datos: puedes intentarlo todas las veces que quieras.</p>
      <div className="grid-2">
        {CHALLENGES.map((c, i) => (
          <motion.div key={c.id} className="card challenge-card" initial={{ opacity: 0, y: 10 }} whileInView={{ opacity: 1, y: 0 }} viewport={{ once: true }} transition={{ delay: i * 0.04 }}>
            <div className="cheat-head">
              <Badge tone={levelTone(c.level)}>{c.level}</Badge>
              {progress.challenges[c.id] ? <Badge tone="success">Superado ✓</Badge> : <span className="muted small">{c.tests.length} tests</span>}
            </div>
            <h3>{i + 1}. {c.title}</h3>
            <p className="muted">{c.intro}</p>
            <div className="small muted mb-8">{DB_INFO[c.db].emoji} Base de datos: {DB_INFO[c.db].label}</div>
            <Btn onClick={() => navigate("desafios/" + c.id)}>Abrir desafío →</Btn>
          </motion.div>
        ))}
      </div>
    </div>
  );
}

function ChallengeDetail({ id }) {
  const { progress, markDone } = useApp();
  const ch = CHALLENGES.find((c) => c.id === id);
  if (!ch) return <div className="page"><h1 className="page-title">Desafío no encontrado</h1><Btn variant="ghost" onClick={() => navigate("desafios")}>Volver a desafíos</Btn></div>;
  const idx = CHALLENGES.indexOf(ch);
  const next = idx < CHALLENGES.length - 1 ? CHALLENGES[idx + 1] : null;
  return (
    <div className="page lesson-page">
      <div className="lesson-head-bar">
        <a className="back-link" href="#/desafios">← Todos los desafíos</a>
        <div>
          <Badge tone={levelTone(ch.level)}>{ch.level}</Badge>
          {progress.challenges[ch.id] && <span className="ml-8"><Badge tone="success">Superado</Badge></span>}
        </div>
      </div>
      <h1 className="page-title">{ch.title}</h1>
      <p className="page-sub">{ch.intro}</p>
      <div className="card goals-card">
        <h3>Objetivos</h3>
        <ul className="lesson-list">{ch.goals.map((g, i) => <li key={i}>{inlineFmt(g)}</li>)}</ul>
        <div className="small muted">Base de datos: {DB_INFO[ch.db].emoji} {DB_INFO[ch.db].label} — pestaña Esquema del editor para ver tablas y columnas.</div>
      </div>
      <ExerciseCard
        dbKey={ch.db}
        prompt={"Escribe el script SQL completo que resuelve el desafío. Se ejecutará sobre una copia limpia de la base “" + DB_INFO[ch.db].label + "” y se validarán " + ch.tests.length + " tests."}
        initialSql={ch.initialSql}
        hint={ch.hint}
        solution={ch.solution}
        tests={ch.tests}
        completed={!!progress.challenges[ch.id]}
        onPassed={() => markDone("challenges", ch.id)}
      />
      <div className="lesson-nav">
        <Btn variant="ghost" onClick={() => navigate("desafios")}>← Lista</Btn>
        {next && <Btn onClick={() => navigate("desafios/" + next.id)}>{next.title} →</Btn>}
      </div>
    </div>
  );
}

function SchemaView({ dbKey }) {
  const { dbs, setEditorSql } = useApp();
  const db = dbs[dbKey];
  return (
    <div>
      <div className="schema-intro small muted">{DB_INFO[dbKey].emoji} {DB_INFO[dbKey].desc}</div>
      <div className="schema">
        {Object.keys(db.tables).map((t) => {
          const tb = db.tables[t];
          return (
            <div key={t} className="schema-table">
              <div className="schema-head">
                <strong>{t}</strong>
                <span className="muted small">{tb.rows.length} filas</span>
              </div>
              <ul className="schema-cols">
                {tb.columns.map((c) => (
                  <li key={c.name}>
                    <span className="col-name">{c.name}</span>
                    <span className="col-type">{c.type}</span>
                    {c.primaryKey && <span className="pk" title="Clave primaria">PK</span>}
                    {c.notNull && !c.primaryKey && <span className="pk nn" title="NOT NULL">NN</span>}
                  </li>
                ))}
              </ul>
              <button type="button" className="btn-mini" onClick={() => setEditorSql("SELECT * FROM " + t + " LIMIT 10;")}>SELECT * → editor</button>
            </div>
          );
        })}
      </div>
    </div>
  );
}

function Playground() {
  const { dbs, runSql, resetDb, history, clearHistory, editorDb, setEditorDb, editorSql, setEditorSql } = useApp();
  const [out, setOut] = useState(null);
  const [tab, setTab] = useState("resultados");

  const run = useCallback(() => {
    const res = runSql(editorDb, editorSql);
    setOut(res);
    setTab(res.ok ? (res.results.length ? "resultados" : "mensajes") : "mensajes");
  }, [runSql, editorDb, editorSql]);

  const rowsResults = out ? out.results.filter((r) => r.kind === "rows") : [];

  return (
    <div className="page playground">
      <div className="pg-toolbar">
        <div className="pg-db">
          <label htmlFor="db-select" className="small muted">Base de datos</label>
          <select id="db-select" value={editorDb} onChange={(e) => { setEditorDb(e.target.value); setOut(null); }}>
            {DB_KEYS.map((k) => <option key={k} value={k}>{DB_INFO[k].emoji} {DB_INFO[k].label}</option>)}
          </select>
        </div>
        <div className="pg-actions">
          <Btn onClick={run} title="Ctrl/⌘ + Enter">▶ Ejecutar</Btn>
          <Btn variant="ghost" onClick={() => { if (window.confirm("¿Restaurar la base “" + DB_INFO[editorDb].label + "” a sus datos originales?")) resetDb(editorDb); }}>Reiniciar BD</Btn>
          <Btn variant="ghost" onClick={() => setEditorSql("")}>Limpiar</Btn>
        </div>
      </div>
      <SqlEditor value={editorSql} onChange={setEditorSql} onRun={run} height={230} editorId="pg-editor" />
      <div className="small muted pg-hint">Atajos: Ctrl/⌘ + Enter ejecuta · Tab inserta espacios · varias sentencias separadas por “;” se ejecutan en orden.</div>

      <div className="tabs" role="tablist">
        {[["resultados", "Resultados"], ["mensajes", "Mensajes"], ["esquema", "Esquema"], ["historial", "Historial (" + history.length + ")"]].map((t) => (
          <button key={t[0]} role="tab" aria-selected={tab === t[0]} type="button"
            className={"tab" + (tab === t[0] ? " active" : "")} onClick={() => setTab(t[0])}>{t[1]}</button>
        ))}
      </div>

      <div className="panel card">
        {tab === "resultados" && (
          <div>
            {!out && <div className="empty-state">Ejecuta una consulta para ver aquí los resultados. Prueba con <code className="inline-code">SELECT * FROM {editorDb === "tienda" ? "clientes" : editorDb === "empleados" ? "empleados" : "libros"};</code></div>}
            {out && out.error && <ErrorBanner error={out.error} />}
            {out && !out.error && rowsResults.length === 0 && <MessageList messages={out.messages} />}
            {out && rowsResults.map((r, i) => (
              <div key={i} className="result-block">
                <div className="result-meta small muted">
                  {r.rowCount} fila{r.rowCount === 1 ? "" : "s"} · {out.ms} ms{r.truncated ? " · resultado truncado a " + MAX_ROWS : ""}
                </div>
                <DataTable columns={r.columns} rows={r.rows} />
              </div>
            ))}
            {out && rowsResults.length > 0 && out.messages.length > 0 && <MessageList messages={out.messages} />}
          </div>
        )}
        {tab === "mensajes" && (
          <div>
            {out && out.error && <ErrorBanner error={out.error} />}
            <MessageList messages={out ? out.messages : []} />
            {!out && <div className="empty-state">Los mensajes de éxito, aviso y error aparecerán aquí.</div>}
          </div>
        )}
        {tab === "esquema" && <SchemaView dbKey={editorDb} />}
        {tab === "historial" && (
          <div>
            {history.length === 0 && <div className="empty-state">Aún no has ejecutado consultas. El historial guarda las últimas 60.</div>}
            {history.length > 0 && (
              <div className="history-bar">
                <Btn variant="ghost" onClick={clearHistory}>Vaciar historial</Btn>
              </div>
            )}
            <ul className="history-list">
              {history.map((h) => (
                <li key={h.id} className={"history-item " + (h.ok ? "ok" : "err")}>
                  <div className="history-line">
                    <span className={"dot " + (h.ok ? "dot-ok" : "dot-err")} title={h.ok ? "Éxito" : "Error"} />
                    <code className="history-sql">{h.sql.trim().replace(/\s+/g, " ").slice(0, 120)}{h.sql.length > 120 ? "…" : ""}</code>
                  </div>
                  <div className="history-meta small muted">
                    {DB_INFO[h.dbKey].emoji} {DB_INFO[h.dbKey].label} · {fmtTime(h.at)} · {h.ms} ms · {h.summary}
                  </div>
                  <div className="history-actions">
                    <button type="button" className="btn-mini" onClick={() => { setEditorSql(h.sql); setEditorDb(h.dbKey); }}>Cargar en editor</button>
                    <CopyButton text={h.sql} />
                  </div>
                </li>
              ))}
            </ul>
          </div>
        )}
      </div>
    </div>
  );
}

function TestsView() {
  const [run, setRun] = useState(null);
  const [running, setRunning] = useState(false);
  const exec = useCallback(() => {
    setRunning(true);
    setTimeout(() => { setRun(runTestSuite()); setRunning(false); }, 30);
  }, []);
  useEffect(() => { exec(); }, [exec]);
  const groups = [];
  if (run) run.results.forEach((r) => { if (groups.indexOf(r.group) === -1) groups.push(r.group); });
  return (
    <div className="page">
      <h1 className="page-title">Tests del motor SQL</h1>
      <p className="page-sub">
        Suite de pruebas que se ejecuta en tu navegador sobre el mismo motor que usa el editor. Cubre validación y
        seguridad, ejecución de consultas, manejo de errores y contrato de experiencia de usuario. En el repositorio,
        estas pruebas se replican con vitest y node:test (ver <a href="#/docs">Docs</a>).
      </p>
      <div className="test-toolbar">
        <Btn onClick={exec} disabled={running}>{running ? "Ejecutando…" : "↻ Volver a ejecutar"}</Btn>
        {run && (
          <div className="test-summary">
            <span className="ts-item"><strong>{run.passed}</strong> pasan</span>
            <span className={"ts-item " + (run.failed ? "ts-bad" : "ts-good")}><strong>{run.failed}</strong> fallan</span>
            <span className="ts-item"><strong>{run.total}</strong> totales</span>
            <span className="ts-item muted">{run.ms} ms</span>
          </div>
        )}
      </div>
      {run && run.failed === 0 && <div className="msg msg-success"><span className="msg-icon">✓</span><span>Todos los tests pasan. El motor está listo para producción.</span></div>}
      {run && groups.map((g) => {
        const items = run.results.filter((r) => r.group === g);
        const fails = items.filter((r) => r.status === "fail").length;
        return (
          <section key={g} className="section">
            <div className="section-head">
              <h2 className="section-title-sm">{g}</h2>
              <span className={fails ? "badge badge-error" : "badge badge-success"}>{fails ? fails + " fallo(s)" : "todo OK"}</span>
            </div>
            <ul className="test-rows">
              {items.map((r, i) => (
                <li key={i} className={"test-row " + r.status}>
                  <span className="test-icon">{r.status === "pass" ? "✓" : "✕"}</span>
                  <span className="test-name">{r.name}</span>
                  <span className="test-ms muted small">{r.ms} ms</span>
                  {r.status === "fail" && <div className="test-err-block">{r.error}</div>}
                </li>
              ))}
            </ul>
          </section>
        );
      })}
    </div>
  );
}

function DocsView() {
  return (
    <div className="page docs">
      <h1 className="page-title">Documentación</h1>
      <p className="page-sub">Guía completa para instalar, ejecutar, testear, desplegar y extender la plataforma.</p>
      {DOCS_SECTIONS.map((s, i) => (
        <section key={i} className="section doc-section">
          <h2 className="section-title-sm">{s.title}</h2>
          {s.blocks.map((b, j) => {
            if (b.k === "p") return <p key={j} className="lesson-p">{inlineFmt(b.text)}</p>;
            if (b.k === "note") return <div key={j} className="callout">{inlineFmt(b.text)}</div>;
            if (b.k === "list") return <ul key={j} className="lesson-list">{b.items.map((it, x) => <li key={x}>{inlineFmt(it)}</li>)}</ul>;
            if (b.k === "code") return <CodeBlock key={j} sql={b.code} lang={b.lang || "code"} />;
            return null;
          })}
        </section>
      ))}
    </div>
  );
}

function NotFound() {
  return (
    <div className="page empty-state">
      <h1 className="page-title">Página no encontrada</h1>
      <p className="muted">La ruta solicitada no existe.</p>
      <Btn onClick={() => navigate("")}>Ir al inicio</Btn>
    </div>
  );
}

/* ---------- Header / Footer ---------- */

const NAV = [
  ["", "Inicio"], ["lecciones", "Lecciones"], ["referencia", "Referencia"],
  ["desafios", "Desafíos"], ["editor", "Editor"], ["tests", "Tests"], ["docs", "Docs"]
];

function Logo() {
  return (
    <a className="brand" href="#/" aria-label="SQLab — inicio">
      <svg width="26" height="26" viewBox="0 0 24 24" fill="none" aria-hidden="true">
        <ellipse cx="12" cy="5.5" rx="8" ry="3" stroke="currentColor" strokeWidth="1.8" />
        <path d="M4 5.5v6c0 1.66 3.58 3 8 3s8-1.34 8-3v-6" stroke="currentColor" strokeWidth="1.8" />
        <path d="M4 11.5v6c0 1.66 3.58 3 8 3s8-1.34 8-3v-6" stroke="currentColor" strokeWidth="1.8" />
      </svg>
      <span className="brand-name">SQLab</span>
    </a>
  );
}

function Header() {
  const parts = useRoute();
  const [open, setOpen] = useState(false);
  const active = parts.length ? parts[0] : "";
  useEffect(() => { setOpen(false); }, [parts.join("/")]);
  return (
    <header className="header">
      <div className="container header-inner">
        <Logo />
        <nav className="nav" aria-label="Navegación principal">
          {NAV.map((n) => (
            <a key={n[0]} href={"#/" + n[0]} className={"nav-link" + (active === n[0] ? " active" : "")}
              aria-current={active === n[0] ? "page" : undefined}>{n[1]}</a>
          ))}
        </nav>
        <button type="button" className="hamburger" aria-label="Abrir menú" aria-expanded={open} onClick={() => setOpen(!open)}>
          <span /><span /><span />
        </button>
      </div>
      {open && (
        <nav className="mobile-nav" aria-label="Navegación móvil">
          {NAV.map((n) => (
            <a key={n[0]} href={"#/" + n[0]} className={"nav-link" + (active === n[0] ? " active" : "")}>{n[1]}</a>
          ))}
        </nav>
      )}
    </header>
  );
}

function Footer() {
  return (
    <footer className="footer">
      <div className="container footer-inner">
        <span className="muted small">SQLab · Plataforma educativa de SQL · El motor se ejecuta íntegramente en tu navegador.</span>
        <span className="footer-links">
          <a href="#/docs">Documentación</a> · <a href="#/tests">Tests</a> · <a href="#/referencia">Referencia</a>
        </span>
      </div>
    </footer>
  );
}

/* ============================================================================
 * APP
 * ========================================================================== */

export default function App() {
  const [dbs, setDbs] = useState(() => ({
    tienda: freshDb("tienda"),
    empleados: freshDb("empleados"),
    biblioteca: freshDb("biblioteca")
  }));
  const [history, setHistory] = useState([]);
  const [progress, setProgress] = useState(loadProgress);
  const [editorDb, setEditorDb] = useState("tienda");
  const [editorSql, setEditorSql] = useState(
    "-- ¡Bienvenido al editor de SQLab! Pulsa ▶ Ejecutar o Ctrl/⌘+Enter.\n" +
    "SELECT c.nombre, p.fecha, p.estado\nFROM pedidos p\nJOIN clientes c ON c.id = p.cliente_id\nORDER BY p.fecha DESC\nLIMIT 5;"
  );
  const parts = useRoute();
  const routeKey = parts.join("/") || "home";

  useEffect(() => { injectFonts(); }, []);
  useEffect(() => {
    try { window.localStorage.setItem("sqlab:progress", JSON.stringify(progress)); } catch (e) { /* sin persistencia */ }
  }, [progress]);

  const runSql = useCallback((dbKey, sql) => {
    const key = DB_SEEDS[dbKey] ? dbKey : "tienda";
    const db = dbs[key];
    const out = executeScript(db, sql);
    setDbs((prev) => Object.assign({}, prev, { [key]: Object.assign({}, db) }));
    setHistory((prev) => [{
      id: Date.now() + "-" + Math.floor(Math.random() * 10000),
      sql, dbKey: key, at: Date.now(), ok: out.ok, ms: out.ms, summary: summarize(out)
    }, ...prev].slice(0, 60));
    return out;
  }, [dbs]);

  const resetDb = useCallback((dbKey) => {
    setDbs((prev) => Object.assign({}, prev, { [dbKey]: freshDb(dbKey) }));
  }, []);

  const markDone = useCallback((kind, id) => {
    setProgress((prev) => {
      const next = { lessons: Object.assign({}, prev.lessons), challenges: Object.assign({}, prev.challenges) };
      next[kind][id] = true;
      return next;
    });
  }, []);

  const openInEditor = useCallback((sql, dbKey) => {
    setEditorSql(sql);
    if (dbKey) setEditorDb(dbKey);
    navigate("editor");
  }, []);

  const clearHistory = useCallback(() => setHistory([]), []);

  const ctx = useMemo(() => ({
    dbs, runSql, resetDb, history, clearHistory, progress, markDone,
    editorDb, setEditorDb, editorSql, setEditorSql, openInEditor
  }), [dbs, runSql, resetDb, history, clearHistory, progress, markDone, editorDb, editorSql, openInEditor]);

  const route = parts[0] || "";
  let view;
  if (!route) view = <Home />;
  else if (route === "lecciones") view = parts[1] ? <LessonDetail id={parts[1]} /> : <LessonsIndex />;
  else if (route === "referencia") view = <CheatsheetView />;
  else if (route === "desafios") view = parts[1] ? <ChallengeDetail id={parts[1]} /> : <ChallengesIndex />;
  else if (route === "editor") view = <Playground />;
  else if (route === "tests") view = <TestsView />;
  else if (route === "docs") view = <DocsView />;
  else view = <NotFound />;

  return (
    <AppCtx.Provider value={ctx}>
      <style>{CSS}</style>
      <a className="skip-link" href="#main">Saltar al contenido</a>
      <Header />
      <main id="main" className="container">
        <AnimatePresence mode="wait">
          <motion.div key={routeKey}
            initial={{ opacity: 0, y: 8 }} animate={{ opacity: 1, y: 0 }} exit={{ opacity: 0 }}
            transition={{ duration: 0.22 }}>
            {view}
          </motion.div>
        </AnimatePresence>
      </main>
      <Footer />
    </AppCtx.Provider>
  );
}

/* ============================================================================
 * ESTILOS — paleta neutra con acento índigo, tipografía Inter + JetBrains Mono
 * ========================================================================== */

const CSS = `
:root{
  --bg:#ffffff; --bg-alt:#f7f7f8; --panel:#ffffff;
  --border:#e5e5e8; --border-strong:#d4d4d8;
  --text:#18181b; --muted:#6b6b72; --faint:#9a9aa1;
  --accent:#4f46e5; --accent-soft:#eef0ff; --accent-hover:#4338ca;
  --success:#15803d; --success-soft:#ecfdf3; --success-border:#bbf7d0;
  --error:#b91c1c; --error-soft:#fef2f2; --error-border:#fecaca;
  --warning:#b45309; --warning-soft:#fffbeb; --warning-border:#fde68a;
  --radius:10px; --radius-sm:6px;
  --sans:'Inter',ui-sans-serif,system-ui,-apple-system,'Segoe UI',Roboto,Arial,sans-serif;
  --mono:'JetBrains Mono',ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;
  --shadow:0 1px 2px rgba(0,0,0,.04),0 4px 16px rgba(0,0,0,.05);
}
*{box-sizing:border-box}
html,body{margin:0;padding:0}
body{font-family:var(--sans);color:var(--text);background:var(--bg-alt);font-size:15px;line-height:1.6;-webkit-font-smoothing:antialiased}
a{color:var(--accent);text-decoration:none}
a:hover{text-decoration:underline}
h1,h2,h3{line-height:1.25;letter-spacing:-0.01em}
code,.inline-code{font-family:var(--mono)}
.inline-code{background:var(--accent-soft);color:var(--accent-hover);padding:1px 5px;border-radius:4px;font-size:.86em}
.muted{color:var(--muted)} .small{font-size:13px} .mb-4{margin-bottom:4px} .mb-8{margin-bottom:8px} .ml-8{margin-left:8px} .mt-8{margin-top:8px}
.container{max-width:1120px;margin:0 auto;padding:0 20px}
.skip-link{position:absolute;left:-9999px;top:0;background:var(--accent);color:#fff;padding:8px 14px;z-index:200;border-radius:0 0 8px 0}
.skip-link:focus{left:0}
:focus-visible{outline:2px solid var(--accent);outline-offset:2px;border-radius:4px}

/* Header */
.header{position:sticky;top:0;z-index:100;background:rgba(255,255,255,.92);backdrop-filter:blur(8px);border-bottom:1px solid var(--border)}
.header-inner{display:flex;align-items:center;justify-content:space-between;height:60px;gap:16px}
.brand{display:flex;align-items:center;gap:9px;color:var(--text);font-weight:700}
.brand:hover{text-decoration:none}
.brand svg{color:var(--accent)}
.brand-name{font-size:17px;letter-spacing:-.02em}
.nav{display:flex;gap:4px}
.nav-link{padding:7px 12px;border-radius:var(--radius-sm);color:var(--muted);font-weight:500;font-size:14px}
.nav-link:hover{color:var(--text);background:var(--bg-alt);text-decoration:none}
.nav-link.active{color:var(--accent);background:var(--accent-soft)}
.hamburger{display:none;background:none;border:1px solid var(--border);border-radius:var(--radius-sm);padding:8px 9px;cursor:pointer;flex-direction:column;gap:4px}
.hamburger span{display:block;width:18px;height:2px;background:var(--text);border-radius:2px}
.mobile-nav{display:none;border-top:1px solid var(--border);background:#fff;padding:8px 20px 14px}
.mobile-nav .nav-link{display:block;padding:10px 8px;font-size:15px}

/* Botones y badges */
.btn{display:inline-flex;align-items:center;gap:6px;border:1px solid transparent;border-radius:var(--radius-sm);padding:9px 16px;font:600 14px var(--sans);cursor:pointer;transition:all .15s ease;background:var(--accent);color:#fff}
.btn:hover{background:var(--accent-hover)}
.btn:disabled{opacity:.55;cursor:not-allowed}
.btn-ghost{background:#fff;border-color:var(--border-strong);color:var(--text)}
.btn-ghost:hover{background:var(--bg-alt);border-color:var(--faint)}
.btn-mini{background:#fff;border:1px solid var(--border);border-radius:var(--radius-sm);padding:4px 10px;font:500 12px var(--sans);color:var(--muted);cursor:pointer}
.btn-mini:hover{color:var(--text);border-color:var(--border-strong)}
.badge{display:inline-flex;align-items:center;padding:3px 10px;border-radius:99px;font-size:12px;font-weight:600;border:1px solid transparent}
.badge-neutral{background:var(--bg-alt);border-color:var(--border);color:var(--muted)}
.badge-basico{background:#ecfdf5;border-color:#a7f3d0;color:#047857}
.badge-intermedio{background:#eff6ff;border-color:#bfdbfe;color:#1d4ed8}
.badge-avanzado{background:#faf5ff;border-color:#e9d5ff;color:#7e22ce}
.badge-success{background:var(--success-soft);border-color:var(--success-border);color:var(--success)}
.badge-error{background:var(--error-soft);border-color:var(--error-border);color:var(--error)}

/* Páginas y secciones */
main.container{padding-top:28px;padding-bottom:60px;min-height:70vh}
.page{padding:8px 0 24px}
.page-title{font-size:30px;margin:6px 0 6px;font-weight:700}
.page-sub{color:var(--muted);margin:0 0 22px;max-width:760px}
.section{margin:38px 0}
.section-title{font-size:22px;margin:0 0 8px}
.section-title-sm{font-size:17px;margin:0 0 12px}
.section-sub{color:var(--muted);max-width:760px;margin:0 0 18px}
.section-head{display:flex;align-items:center;justify-content:space-between;gap:12px;margin-bottom:10px}
.card{background:var(--panel);border:1px solid var(--border);border-radius:var(--radius);padding:18px;box-shadow:var(--shadow)}
.grid-2{display:grid;grid-template-columns:1fr 1fr;gap:16px}
.grid-3{display:grid;grid-template-columns:repeat(3,1fr);gap:16px}
.grid-4{display:grid;grid-template-columns:repeat(4,1fr);gap:16px}
.empty-state{padding:28px;text-align:center;color:var(--muted);border:1px dashed var(--border-strong);border-radius:var(--radius);background:#fff}

/* Hero */
.hero{padding:52px 0 8px}
.hero-badge{display:inline-block;background:var(--accent-soft);color:var(--accent-hover);border:1px solid #dfe3ff;padding:5px 12px;border-radius:99px;font-size:12.5px;font-weight:600;margin-bottom:18px}
.hero-title{font-size:44px;line-height:1.12;margin:0 0 14px;font-weight:800;letter-spacing:-.025em;max-width:760px}
.hero-sub{color:var(--muted);font-size:17px;max-width:680px;margin:0 0 24px}
.hero-cta{display:flex;gap:12px;flex-wrap:wrap;margin-bottom:30px}
.hero-stats{display:flex;gap:26px;flex-wrap:wrap;border-top:1px solid var(--border);padding-top:18px}
.stat{display:flex;flex-direction:column}
.stat strong{font-size:22px;letter-spacing:-.02em}
.stat span{color:var(--muted);font-size:12.5px}
.feature-card h3{margin:0 0 6px;font-size:15px}
.feature-card p{margin:0;font-size:13.5px}
.level-card .level-head{display:flex;justify-content:space-between;align-items:center;margin-bottom:10px}
.progress{height:6px;background:var(--bg-alt);border:1px solid var(--border);border-radius:99px;overflow:hidden;margin-bottom:12px}
.progress-fill{height:100%;background:var(--accent);border-radius:99px;transition:width .4s ease}
.level-list{list-style:none;margin:0 0 8px;padding:0}
.level-list li{padding:5px 0;border-bottom:1px dashed var(--border);font-size:14px}
.level-list li:last-child{border-bottom:0}
.level-list a{color:var(--text)}
.tick{color:var(--success);font-weight:700;margin-right:4px}
.note-card h3{margin:0 0 8px}

/* Lecciones */
.lesson-list{display:flex;flex-direction:column;gap:8px}
.lesson-row{display:flex;align-items:center;gap:14px;width:100%;text-align:left;background:#fff;border:1px solid var(--border);border-radius:var(--radius);padding:13px 16px;cursor:pointer;font:inherit;transition:border-color .15s, box-shadow .15s}
.lesson-row:hover{border-color:var(--accent);box-shadow:var(--shadow)}
.lesson-num{flex:0 0 30px;height:30px;border-radius:50%;background:var(--bg-alt);border:1px solid var(--border);display:flex;align-items:center;justify-content:center;font-weight:700;font-size:13px;color:var(--muted)}
.lesson-num.done{background:var(--success-soft);border-color:var(--success-border);color:var(--success)}
.lesson-info{display:flex;flex-direction:column;flex:1;min-width:0}
.lesson-title{font-weight:600}
.lesson-sub{color:var(--muted);font-size:13px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.lesson-meta{flex-shrink:0}
.lesson-page{max-width:860px}
.lesson-head-bar{display:flex;justify-content:space-between;align-items:center;gap:12px;margin-bottom:6px}
.back-link{font-size:14px}
.lesson-body .lesson-p{margin:12px 0}
.lesson-list{margin:12px 0;padding-left:0;list-style:none}
.lesson-body .lesson-list{list-style:disc;padding-left:22px}
.lesson-body .lesson-list li{border:0;padding:2px 0}
.callout{background:var(--accent-soft);border:1px solid #dfe3ff;border-radius:var(--radius-sm);padding:12px 14px;margin:14px 0;font-size:14px}
.example-block{margin:18px 0}
.example-caption{color:var(--muted);font-size:13.5px;margin-top:8px}
.lesson-nav{display:flex;justify-content:space-between;gap:12px;margin-top:26px;flex-wrap:wrap}

/* Code blocks */
.codeblock{border:1px solid var(--border);border-radius:var(--radius-sm);overflow:hidden;background:#fbfbfc;margin:6px 0}
.codeblock-bar{display:flex;justify-content:space-between;align-items:center;padding:5px 10px;background:var(--bg-alt);border-bottom:1px solid var(--border)}
.codeblock-lang{font:600 11px var(--mono);color:var(--faint);text-transform:uppercase;letter-spacing:.06em}
.codeblock-pre{margin:0;padding:12px 14px;overflow-x:auto;font:13px/1.65 var(--mono);white-space:pre;color:var(--text)}
.tk-kw{color:#4f46e5;font-weight:700}
.tk-str{color:#15803d}
.tk-num{color:#b45309}
.tk-com{color:#9a9aa1;font-style:italic}
.tk-fn{color:#0e7490;font-weight:600}

/* Editor */
.sqleditor{border:1px solid var(--border-strong);border-radius:var(--radius-sm);background:#fff;overflow:hidden;margin:10px 0}
.sqleditor-inner{display:flex;align-items:stretch}
.editor-gutter{flex:0 0 auto;padding:12px 8px 12px 12px;text-align:right;background:var(--bg-alt);border-right:1px solid var(--border);color:var(--faint);font:13px/1.6 var(--mono);user-select:none;overflow:hidden}
.editor-area{position:relative;flex:1;min-width:0}
.editor-highlight,.editor-area textarea{margin:0;padding:12px 14px;font:13px/1.6 var(--mono);white-space:pre;border:0;tab-size:2}
.editor-highlight{position:absolute;inset:0;overflow:hidden;pointer-events:none;color:var(--text);background:transparent;z-index:1}
.editor-area textarea{position:absolute;inset:0;width:100%;height:100%;resize:none;background:transparent;color:transparent;caret-color:var(--accent);outline:none;overflow:auto;z-index:2}
.editor-area textarea::selection{background:rgba(79,70,229,.18)}
.editor-area textarea::placeholder{color:var(--faint)}

/* Ejercicios */
.exercise{margin-top:22px}
.exercise-head{display:flex;align-items:center;gap:10px;margin-bottom:6px}
.exercise-head h3{margin:0;font-size:16px}
.exercise-prompt{margin:4px 0 6px}
.exercise-db{margin-bottom:8px}
.exercise-actions{display:flex;gap:8px;flex-wrap:wrap;margin:10px 0}
.exercise-out{margin-top:12px;display:flex;flex-direction:column;gap:10px}
.tests-list{list-style:none;margin:8px 0;padding:0;display:flex;flex-direction:column;gap:5px}
.test-item{display:flex;align-items:baseline;gap:8px;font-size:13.5px;padding:6px 10px;border-radius:var(--radius-sm);border:1px solid var(--border)}
.test-item.pass{background:var(--success-soft);border-color:var(--success-border)}
.test-item.fail{background:var(--error-soft);border-color:var(--error-border)}
.test-icon{font-weight:700}
.test-item.pass .test-icon{color:var(--success)}
.test-item.fail .test-icon{color:var(--error)}
.test-err{color:var(--error);font-size:12px}
.goals-card{margin-bottom:18px}
.goals-card h3{margin:0 0 6px;font-size:15px}
.solution{margin-top:8px}

/* Mensajes y errores */
.msg{display:flex;gap:9px;align-items:flex-start;border-radius:var(--radius-sm);padding:10px 13px;font-size:13.5px;border:1px solid;margin:6px 0}
.msg-icon{font-weight:700;flex-shrink:0}
.msg-success{background:var(--success-soft);border-color:var(--success-border);color:var(--success)}
.msg-warning{background:var(--warning-soft);border-color:var(--warning-border);color:var(--warning)}
.msg-error{background:var(--error-soft);border-color:var(--error-border);color:var(--error);display:block}
.msg-title{font-weight:600;display:flex;gap:8px;align-items:baseline}
.msg-hint{margin-top:5px;color:#7f1d1d;font-size:13px}
.msg-list{display:flex;flex-direction:column;gap:4px}

/* Playground */
.playground{max-width:1000px}
.pg-toolbar{display:flex;justify-content:space-between;align-items:flex-end;gap:12px;flex-wrap:wrap;margin-bottom:4px}
.pg-db{display:flex;flex-direction:column;gap:3px}
.pg-db select{font:500 14px var(--sans);padding:8px 10px;border:1px solid var(--border-strong);border-radius:var(--radius-sm);background:#fff;color:var(--text)}
.pg-actions{display:flex;gap:8px;flex-wrap:wrap}
.pg-hint{margin:2px 0 14px}
.tabs{display:flex;gap:2px;border-bottom:1px solid var(--border);margin:18px 0 12px;flex-wrap:wrap}
.tab{background:none;border:0;border-bottom:2px solid transparent;padding:9px 14px;font:600 13.5px var(--sans);color:var(--muted);cursor:pointer}
.tab:hover{color:var(--text)}
.tab.active{color:var(--accent);border-bottom-color:var(--accent)}
.panel{min-height:180px}
.result-block{margin-bottom:18px}
.result-meta{margin-bottom:5px}

/* Tablas de datos */
.table-wrap{overflow:auto;border:1px solid var(--border);border-radius:var(--radius-sm);background:#fff;max-height:420px}
.data-table{border-collapse:collapse;width:100%;font-size:13px}
.data-table th{position:sticky;top:0;background:var(--bg-alt);text-align:left;padding:8px 12px;border-bottom:1px solid var(--border-strong);font:600 12.5px var(--mono);color:var(--muted);white-space:nowrap;z-index:2}
.data-table td{padding:7px 12px;border-bottom:1px solid var(--border);white-space:nowrap;max-width:340px;overflow:hidden;text-overflow:ellipsis}
.data-table tbody tr:hover{background:#fafaff}
.data-table tbody tr:last-child td{border-bottom:0}
.rownum{color:var(--faint);font-size:11.5px;text-align:right;width:34px;min-width:34px}
.cell-num{text-align:right;font-family:var(--mono);font-size:12.5px}
.cell-null{color:var(--faint);font-style:italic;font-family:var(--mono);font-size:12px}
.empty-cell{color:var(--muted);font-style:italic;text-align:center;padding:18px}
.table-more{padding:7px 12px;color:var(--muted);font-size:12.5px;border-top:1px solid var(--border);background:var(--bg-alt)}
.live-result{margin-top:8px}

/* Esquema */
.schema-intro{margin-bottom:10px}
.schema{display:grid;grid-template-columns:repeat(auto-fill,minmax(220px,1fr));gap:12px}
.schema-table{border:1px solid var(--border);border-radius:var(--radius-sm);padding:12px;background:#fff}
.schema-head{display:flex;justify-content:space-between;align-items:baseline;margin-bottom:8px}
.schema-head strong{font-family:var(--mono);font-size:13.5px}
.schema-cols{list-style:none;margin:0 0 10px;padding:0}
.schema-cols li{display:flex;align-items:center;gap:7px;padding:2.5px 0;font-size:12.5px;border-bottom:1px dashed var(--border)}
.schema-cols li:last-child{border-bottom:0}
.col-name{font-family:var(--mono);flex:1}
.col-type{color:var(--faint);font-size:11px;font-family:var(--mono)}
.pk{background:var(--warning-soft);border:1px solid var(--warning-border);color:var(--warning);border-radius:4px;font-size:10px;font-weight:700;padding:0 4px}
.pk.nn{background:var(--bg-alt);border-color:var(--border);color:var(--muted)}

/* Historial */
.history-bar{margin-bottom:10px}
.history-list{list-style:none;margin:0;padding:0;display:flex;flex-direction:column;gap:8px}
.history-item{border:1px solid var(--border);border-radius:var(--radius-sm);padding:10px 12px;background:#fff}
.history-line{display:flex;gap:8px;align-items:baseline}
.dot{width:8px;height:8px;border-radius:50%;flex-shrink:0;display:inline-block}
.dot-ok{background:#22c55e} .dot-err{background:#ef4444}
.history-sql{font:12.5px/1.5 var(--mono);color:var(--text);word-break:break-all}
.history-meta{margin:4px 0 6px 16px}
.history-actions{display:flex;gap:6px;margin-left:16px}

/* Referencia */
.search-input{width:100%;max-width:480px;padding:10px 14px;border:1px solid var(--border-strong);border-radius:var(--radius-sm);font:14px var(--sans);margin-bottom:6px;background:#fff}
.cheat-card{display:flex;flex-direction:column;gap:6px}
.cheat-head{display:flex;justify-content:space-between;align-items:center;gap:8px}
.cheat-cmd{font:700 14px var(--mono);color:var(--accent-hover)}
.cheat-syntax{background:var(--bg-alt);border:1px solid var(--border);border-radius:var(--radius-sm);padding:7px 10px;font:12.5px var(--mono);overflow-x:auto}
.cheat-syntax code{white-space:pre}
.cheat-card p{margin:2px 0}
.cheat-actions{margin-top:auto;padding-top:4px}
.challenge-card h3{margin:8px 0 4px;font-size:16px}
.challenge-card p{margin:0 0 8px;font-size:13.5px}

/* Tests */
.test-toolbar{display:flex;align-items:center;gap:18px;flex-wrap:wrap;margin:14px 0 10px}
.test-summary{display:flex;gap:16px;flex-wrap:wrap;font-size:14px}
.ts-item strong{font-size:16px;margin-right:3px}
.ts-good{color:var(--success)} .ts-bad{color:var(--error)}
.test-rows{list-style:none;margin:0;padding:0;border:1px solid var(--border);border-radius:var(--radius-sm);overflow:hidden;background:#fff}
.test-row{display:flex;align-items:baseline;gap:10px;padding:8px 13px;border-bottom:1px solid var(--border);font-size:13.5px;flex-wrap:wrap;position:relative}
.test-row:last-child{border-bottom:0}
.test-row.pass .test-icon{color:var(--success)}
.test-row.fail{background:var(--error-soft)}
.test-row.fail .test-icon{color:var(--error)}
.test-name{flex:1;min-width:200px}
.test-ms{flex-shrink:0}
.test-err-block{flex-basis:100%;color:var(--error);font:12px/1.5 var(--mono);padding-left:24px}

/* Docs */
.docs .doc-section{margin:30px 0}
.docs .lesson-list{list-style:disc;padding-left:22px}
.docs .lesson-list li{border:0;padding:3px 0}
.docs .codeblock-pre{font-size:12.5px;line-height:1.6}

/* Footer */
.footer{border-top:1px solid var(--border);background:#fff;margin-top:40px}
.footer-inner{display:flex;justify-content:space-between;gap:12px;padding:20px;flex-wrap:wrap}
.footer-links a{color:var(--muted)}

/* Responsive */
@media (max-width:960px){
  .grid-4{grid-template-columns:1fr 1fr}
  .grid-3{grid-template-columns:1fr}
  .hero-title{font-size:34px}
}
@media (max-width:760px){
  .nav{display:none}
  .hamburger{display:flex}
  .mobile-nav{display:flex;flex-direction:column}
  .grid-2{grid-template-columns:1fr}
  .grid-4{grid-template-columns:1fr}
  .hero{padding-top:34px}
  .hero-title{font-size:29px}
  .hero-sub{font-size:15px}
  .pg-toolbar{flex-direction:column;align-items:stretch}
  .lesson-sub{white-space:normal}
  .page-title{font-size:24px}
}
`;
