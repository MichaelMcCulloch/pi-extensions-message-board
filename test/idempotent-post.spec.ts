import { mkdtempSync,rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { it,expect } from 'vitest';
import { BoardStore } from '../src/extension/store.ts';
import { SqliteBoardBackend } from '../src/extension/sqlite.ts';
it('deduplicates across SQLite connections and refuses key-content collisions',()=>{
  const dir=mkdtempSync(join(tmpdir(),'board-receipt-'));const file=join(dir,'board.db');
  const b1=new SqliteBoardBackend(file);const b2=new SqliteBoardBackend(file);
  try {
    const a=new BoardStore(b1);const b=new BoardStore(b2);a.register('campaign');
    a.postOnce('campaign','results','receipt','immutable evidence','receipt-1');
    b.postOnce('campaign','results','receipt','immutable evidence','receipt-1');
    expect(a.postCount()).toBe(1);
    expect(()=>b.postOnce('campaign','results','receipt','changed evidence','receipt-1')).toThrow('different content');
    expect(a.postCount()).toBe(1);expect(a.read('results')[0]!.body).toBe('immutable evidence');
  }finally{b1.close();b2.close();rmSync(dir,{recursive:true,force:true});}
});
