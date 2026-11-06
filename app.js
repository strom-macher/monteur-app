(function(){'use strict';
/* strom-macher Monteur-App · Datenschicht: lokaler Speicher (IndexedDB), Warteschlange, Abgleich mit Supabase */
var CFG=window.SM_CONFIG||{};
var $=function(s,r){return (r||document).querySelector(s)};
var esc=function(s){return String(s==null?'':s).replace(/[&<>"']/g,function(c){return {'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]})};
var pad=function(n){return String(n).padStart(2,'0')};
var iso=function(d){return d.getFullYear()+'-'+pad(d.getMonth()+1)+'-'+pad(d.getDate())};
var dayOff=function(n){var d=new Date();d.setDate(d.getDate()+n);return iso(d)};
var TODAY=function(){return iso(new Date())};
var nf=function(n,d){return Number(n).toLocaleString('de-AT',{maximumFractionDigits:d==null?1:d})};
var uuid=function(){
  if(window.crypto&&crypto.randomUUID)return crypto.randomUUID();
  var b=new Uint8Array(16);crypto.getRandomValues(b);b[6]=b[6]&15|64;b[8]=b[8]&63|128;
  var h=[].map.call(b,function(x){return x.toString(16).padStart(2,'0')}).join('');
  return h.slice(0,8)+'-'+h.slice(8,12)+'-'+h.slice(12,16)+'-'+h.slice(16,20)+'-'+h.slice(20);
};
var msOf=function(s){var t=Date.parse(s);return isNaN(t)?0:t};

/* ---------- IndexedDB (Schlüssel/Wert) ---------- */
var idb=(function(){
  var db=null,mem={};
  function open(){
    return new Promise(function(res){
      try{
        var r=indexedDB.open('sm-app',1);
        r.onupgradeneeded=function(){r.result.createObjectStore('kv')};
        r.onsuccess=function(){db=r.result;res()};
        r.onerror=function(){res()};
      }catch(e){res()}
    });
  }
  function tx(mode,fn){
    return new Promise(function(res){
      if(!db){res(fn===null?undefined:undefined);return}
      try{var t=db.transaction('kv',mode),st=t.objectStore('kv'),rq=fn(st);t.oncomplete=function(){res(rq&&rq.result)};t.onerror=t.onabort=function(){res()}}catch(e){res()}
    });
  }
  return {
    open:open,
    get:function(k){if(!db)return Promise.resolve(mem[k]);return tx('readonly',function(s){return s.get(k)})},
    set:function(k,v){if(!db){mem[k]=v;return Promise.resolve()}return tx('readwrite',function(s){return s.put(v,k)})},
    del:function(k){if(!db){delete mem[k];return Promise.resolve()}return tx('readwrite',function(s){return s.delete(k)})},
    clear:function(){mem={};if(!db)return Promise.resolve();return tx('readwrite',function(s){return s.clear()})}
  };
})();

/* ---------- Tabellen ---------- */
var TABLES=['profiles','projects','tasks','hours','photos','materials','material_costs','stock_moves','delivery_suppliers','leads','lead_log'];
var COLS={
  profiles:['id','name','role','active'],
  projects:['id','kundennr','name','short','addr','phone','phone2','email','note','termin','status','created_at'],
  tasks:['id','name','project_id','assignee','due','due_time','done','done_at','created_by','created_at'],
  photos:['id','project_id','path','taken_at','created_by'],
  hours:['id','project_id','work_date','h','note','created_by','created_at'],
  materials:['id','name','unit','min_stock','note'],
  material_costs:['material_id','price','supplier','artnr'],
  stock_moves:['id','material_id','project_id','qty','kind','loc','note','created_by','created_at'],
  delivery_suppliers:['move_id','supplier'],
  leads:['id','name','short','anrede','phone','phone2','email','addr','ort','objekt','ausrichtung','dach','verbrauch','speicher','wuensche','budget','umsetzung','personen','eingang','info','last_info','kwp_basis','kwp_est','kwp','source','lat','lon','km','min','status','status_at','termin','invite_at','invite_termin','notiz','notiz_at','src_hist','sparte','created_at','created_by'],
  lead_log:['id','lead_id','text','at','created_by','by_name']
};
var LOCS=[{k:'haupt',n:'Hauptlager'},{k:'buero',n:'Büro'},{k:'gross',n:'Großwagen'},{k:'klein',n:'Kleinwagen'}];
var LOCK=LOCS.map(function(l){return l.k});
var locName=function(k){for(var i=0;i<LOCS.length;i++)if(LOCS[i].k===k)return LOCS[i].n;return 'Hauptlager'};
var locOf=function(m){return LOCK.indexOf(m.loc)>=0?m.loc:'haupt'};
var PK=function(t){return t==='material_costs'?'material_id':t==='delivery_suppliers'?'move_id':'id'};
function pick(t,row){var o={};COLS[t].forEach(function(c){if(row[c]!==undefined)o[c]=row[c]});return o}
function emptyC(){var c={me:null,pulledAt:0};TABLES.forEach(function(t){c[t]=[]});return c}

var C=emptyC();      /* lokaler Spiegel der Datenbank */
var OB=[];           /* Warteschlange: noch nicht übertragene Änderungen */
var S={projects:[],tasks:[],mats:[],leads:[]};  /* abgeleitete Sicht für die Oberfläche */
var PEOPLE=[];
var ME=null;
var sb=null,SESSION=null;
var sync_={running:false,again:false,err:'',fails:0,last:0};

var persistTimer=null;
function persistC(){clearTimeout(persistTimer);persistTimer=setTimeout(function(){idb.set('C',C)},350)}
function persistOB(){return idb.set('OB',OB)}

/* ---------- Abgeleitete Sicht ---------- */
function initials(n){var p=String(n||'?').trim().split(/\s+/);return ((p[0]||'?')[0]+(p.length>1?p[p.length-1][0]:'')).toUpperCase()}
function build(){
  PEOPLE=C.profiles.filter(function(p){return p.active!==false}).map(function(p){return {id:p.id,name:p.name,role:p.role,ini:initials(p.name),active:p.active!==false}});
  var me=C.me&&C.profiles.filter(function(p){return p.id===C.me.id})[0]||C.me;
  ME=me?{id:me.id,name:me.name,role:me.role,ini:initials(me.name)}:null;

  var costs={},dsup={};
  C.material_costs.forEach(function(c){costs[c.material_id]=c});
  C.delivery_suppliers.forEach(function(d){dsup[d.move_id]=d.supplier});
  var stock={},sloc={},dels={},bk={},tr={};
  C.stock_moves.forEach(function(m){
    var lo=locOf(m),q=Number(m.qty);
    stock[m.material_id]=(stock[m.material_id]||0)+q;
    var sl=sloc[m.material_id]=sloc[m.material_id]||{};sl[lo]=(sl[lo]||0)+q;
    if(m.kind==='anfang'||m.kind==='lieferung'||(m.kind==='korrektur'&&q>0))(dels[m.material_id]=dels[m.material_id]||[]).push({id:m.id,date:iso(new Date(msOf(m.created_at))),at:msOf(m.created_at),qty:q,loc:lo,supplier:dsup[m.id]||'',note:m.kind==='anfang'?'Anfangsbestand':(m.note||''),by:m.created_by});
    if(m.kind==='buchung'&&m.project_id)(bk[m.project_id]=bk[m.project_id]||[]).push({id:m.id,matId:m.material_id,qty:-q,loc:lo,at:msOf(m.created_at),by:m.created_by});
    if(m.kind==='umbuchung')(tr[m.material_id]=tr[m.material_id]||[]).push({id:m.id,qty:q,loc:lo,at:msOf(m.created_at),by:m.created_by,note:m.note||''});
  });
  var r3=function(x){return Math.round((x||0)*1000)/1000};
  S.mats=C.materials.map(function(m){
    var c=costs[m.id]||{};
    var d=(dels[m.id]||[]).sort(function(a,b){return b.at-a.at});
    return {id:m.id,name:m.name,unit:m.unit||'Stk',min:Number(m.min_stock)||0,note:m.note||'',qr:m.qr||'',
      stock:r3(stock[m.id]),locs:LOCK.reduce(function(o,k){o[k]=r3((sloc[m.id]||{})[k]);return o},{}),transfers:(tr[m.id]||[]).sort(function(a,b){return b.at-a.at}),price:Number(c.price)||0,supplier:c.supplier||'',artnr:c.artnr||'',deliveries:d};
  });
  var hrs={},pho={};
  C.hours.forEach(function(h){(hrs[h.project_id]=hrs[h.project_id]||[]).push({id:h.id,date:h.work_date,h:Number(h.h),note:h.note||'',at:msOf(h.created_at),by:h.created_by})});
  C.photos.forEach(function(f){(pho[f.project_id]=pho[f.project_id]||[]).push({id:f.id,path:f.path,at:msOf(f.taken_at),by:f.created_by})});
  S.projects=C.projects.map(function(p){
    var nm=p.name||'';
    return {id:p.id,kundennr:p.kundennr||'',name:nm,label:p.short||nm,addr:p.addr||'',phone:p.phone||'',phone2:p.phone2||'',email:p.email||'',note:p.note||'',
      termin:p.termin||null,status:p.status||'aktiv',created:msOf(p.created_at)||0,
      photos:(pho[p.id]||[]).sort(function(a,b){return a.at-b.at}),
      hours:(hrs[p.id]||[]).sort(function(a,b){return b.at-a.at}),
      mat:(bk[p.id]||[]).sort(function(a,b){return b.at-a.at})};
  });
  S.tasks=C.tasks.map(function(t){
    return {id:t.id,name:t.name,project:t.project_id||null,assignee:t.assignee||null,due:t.due||null,time:t.due_time||'',
      created:msOf(t.created_at),done:!!t.done,doneAt:msOf(t.done_at),by:t.created_by};
  });
  buildLeads();
}

/* ---------- Lokale Änderungen anwenden ---------- */
function idxOf(arr,key,val){for(var i=0;i<arr.length;i++)if(arr[i][key]===val)return i;return -1}
function applyLocal(o){
  var t=o.t;
  if(o.op==='up'||o.op==='photo'){
    var arr=C[t],k=PK(t),i=idxOf(arr,k,o.row[k]);
    if(i<0)arr.push(Object.assign({},o.row));else arr[i]=Object.assign({},arr[i],o.row);
  }else if(o.op==='del'||o.op==='delphoto'){
    var k2=PK(t);C[t]=C[t].filter(function(r){return r[k2]!==o.row[k2]});
    if(t==='materials'){['material_costs'].forEach(function(x){C[x]=C[x].filter(function(r){return r.material_id!==o.row.id})});C.stock_moves=C.stock_moves.filter(function(r){return r.material_id!==o.row.id})}
    if(t==='stock_moves')C.delivery_suppliers=C.delivery_suppliers.filter(function(r){return r.move_id!==o.row.id});
    if(t==='leads')C.lead_log=C.lead_log.filter(function(r){return r.lead_id!==o.row.id});
  }else if(o.op==='rpc'&&o.fn==='set_material_note'){
    var j=idxOf(C.materials,'id',o.args.p_id);if(j>=0)C.materials[j].note=o.args.p_note;
  }
}
function mut(t,op,row,extra){
  if(op==='up'){var ex=C[t][idxOf(C[t],PK(t),row[PK(t)])];row=Object.assign({},ex||{},row)}
  var o=Object.assign({t:t,op:op,row:row},extra||{});
  applyLocal(o);OB.push(o);persistOB();persistC();build();
  if(typeof afterChange==='function')afterChange();
  sync();
}
function mutRpc(fn,args){
  var o={t:'rpc',op:'rpc',fn:fn,args:args};
  applyLocal(o);OB.push(o);persistOB();persistC();build();
  if(typeof afterChange==='function')afterChange();
  sync();
}

/* ---------- Abgleich ---------- */
function errKind(e){
  if(!e)return 'ok';
  var m=String(e.message||e),c=e.code||'';
  if(!c&&/fetch|network|load failed|timeout|abort|offline/i.test(m))return 'net';
  if(e.status===0)return 'net';
  if(c==='PGRST301'||c==='PGRST303'||e.status===401||/jwt/i.test(m))return 'auth';
  if(e.status>=500)return 'net';
  return 'fail';
}
async function sendOp(o){
  try{
    var r;
    if(o.op==='up'){r=await sb.from(o.t).upsert(pick(o.t,o.row),{onConflict:PK(o.t)})}
    else if(o.op==='del'){r=await sb.from(o.t).delete().eq(PK(o.t),o.row[PK(o.t)])}
    else if(o.op==='rpc'){r=await sb.rpc(o.fn,o.args)}
    else if(o.op==='photo'){
      var blob=await idb.get('blob:'+o.row.id);
      if(!blob)return 'fail';
      var u=await sb.storage.from('photos').upload(o.row.path,blob,{contentType:'image/jpeg',upsert:true});
      if(u.error){var k=errKind(u.error);if(k!=='fail')return k;if(!/exists/i.test(u.error.message||''))return 'fail'}
      r=await sb.from('photos').upsert(pick('photos',o.row),{onConflict:'id'});
      if(!r.error)await idb.del('blob:'+o.row.id);
    }
    else if(o.op==='delphoto'){
      var s=await sb.storage.from('photos').remove([o.row.path]);
      if(s.error&&errKind(s.error)!=='fail')return errKind(s.error);
      r=await sb.from('photos').delete().eq('id',o.row.id);
    }
    var kind=errKind(r&&r.error);
    if(kind==='fail'&&r&&r.error)console.warn('Änderung abgelehnt',o.t,o.op,r.error.message);
    return kind;
  }catch(e){return errKind(e)==='fail'?'net':errKind(e)}
}
async function flush(){
  while(OB.length){
    var r=await sendOp(OB[0]);
    if(r==='net'||r==='auth')throw {stop:r};
    var o=OB.shift();
    if(r==='fail'){sync_.fails++;if(o.op==='photo')idb.del('blob:'+o.row.id)}
    await persistOB();
  }
}
async function fetchAll(t){
  var out=[],from=0,step=1000;
  for(;;){
    var q=await sb.from(t).select('*').order(PK(t)).range(from,from+step-1);
    if(q.error){var k=errKind(q.error);throw {stop:k==='fail'?'fail':k,msg:q.error.message,table:t}}
    out=out.concat(q.data||[]);
    if(!q.data||q.data.length<step)break;
    from+=step;
  }
  return out;
}
var lastSig='';
async function pull(){
  var res=await Promise.all(TABLES.map(fetchAll));
  var N={};TABLES.forEach(function(t,i){N[t]=res[i]});
  var before=C;
  C=Object.assign(emptyC(),{me:before.me});
  TABLES.forEach(function(t){C[t]=N[t]});
  OB.forEach(applyLocal);
  C.pulledAt=Date.now();
  var sig=JSON.stringify(TABLES.map(function(t){return C[t]}));
  var changed=sig!==lastSig;lastSig=sig;
  var me=C.profiles.filter(function(p){return SESSION&&p.id===SESSION.user.id})[0];
  if(me)C.me={id:me.id,name:me.name,role:me.role,active:me.active};
  else if(SESSION)C.me={id:SESSION.user.id,name:(SESSION.user.email||'').split('@')[0],role:'',active:false,missing:true};
  persistC();
  return changed;
}
async function sync(){
  if(!sb||!SESSION)return;
  if(sync_.running){sync_.again=true;return}
  if(!navigator.onLine){setStatus();return}
  sync_.running=true;sync_.err='';setStatus();
  var changed=false;
  try{
    await flush();
    changed=await pull();
    sync_.last=Date.now();
    if(sync_.fails){var n=sync_.fails;sync_.fails=0;toast(n+(n===1?' Eintrag wurde':' Einträge wurden')+' vom Server abgelehnt (fehlende Berechtigung?).')}
  }catch(e){
    sync_.err=e&&e.stop||'net';
    if(sync_.err==='auth')await tryRefresh();
    else if(sync_.err==='fail')console.warn('Abgleich fehlgeschlagen',e);
  }
  sync_.running=false;
  build();
  if(changed&&typeof afterChange==='function')afterChange();
  setStatus();
  if(sync_.again){sync_.again=false;setTimeout(sync,60)}
}
async function tryRefresh(){
  try{
    var r=await sb.auth.refreshSession();
    if(r.error&&errKind(r.error)==='fail'){SESSION=null;showAuth('login','Bitte melde dich erneut an.')}
    else if(r.data&&r.data.session){SESSION=r.data.session;setTimeout(sync,200)}
  }catch(e){}
}
var ico={
  search:'<svg width="22" height="22" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round"><circle cx="10.5" cy="10.5" r="6.5"/><path d="M15.5 15.5L21 21"/></svg>',
  x:'<svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round"><path d="M5 5l14 14M19 5L5 19"/></svg>',
  back:'<svg width="22" height="22" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round"><path d="M15 5l-7 7 7 7"/></svg>',
  check:'<svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="#101514" stroke-width="3.2" stroke-linecap="round" stroke-linejoin="round"><path d="M5 12.5l4.5 4.5L19 7.5"/></svg>',
  qr:'<svg width="22" height="22" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linejoin="round"><rect x="3.5" y="3.5" width="6" height="6" rx="1"/><rect x="14.5" y="3.5" width="6" height="6" rx="1"/><rect x="3.5" y="14.5" width="6" height="6" rx="1"/><path d="M14.5 14.5h2.5v2.5M20.5 14.5v.01M14.5 20.5h.01M17.5 20.5h3v-3"/></svg>',
  cam:'<svg width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.1" stroke-linejoin="round"><path d="M4 8h3l1.6-2.5h6.8L17 8h3v11H4z"/><circle cx="12" cy="13" r="3.6"/></svg>',
  img:'<svg width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.1" stroke-linejoin="round"><rect x="3.5" y="4.5" width="17" height="15" rx="2"/><circle cx="9" cy="10" r="1.6"/><path d="M4 18l5-5 4 4 3-3 4 4"/></svg>',
  pin:'<svg width="22" height="22" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.1" stroke-linejoin="round"><path d="M12 21s-6.5-5.6-6.5-11a6.5 6.5 0 0113 0c0 5.4-6.5 11-6.5 11z"/><circle cx="12" cy="10" r="2.4"/></svg>',
  mail:'<svg width="22" height="22" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.1" stroke-linejoin="round"><rect x="3" y="5.5" width="18" height="13" rx="2"/><path d="M3.5 7l8.5 6 8.5-6"/></svg>',
  nav:'<svg width="22" height="22" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.1" stroke-linejoin="round"><path d="M20.5 3.5L3.5 10.5l7 2.5 2.5 7z"/></svg>',
  tel:'<svg width="22" height="22" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.1" stroke-linejoin="round"><path d="M6.5 3.5h3l1.5 4-2 1.5a11 11 0 005.5 5.5l1.5-2 4 1.5v3a2 2 0 01-2 2A15.5 15.5 0 014.5 5.5a2 2 0 012-2z"/></svg>',
  clock:'<svg width="19" height="19" viewBox="0 0 24 24" fill="none" stroke="#101514" stroke-width="2.3" stroke-linecap="round"><circle cx="12" cy="12" r="8.5"/><path d="M12 7.5V12l3 2"/></svg>',
  box:'<svg width="19" height="19" viewBox="0 0 24 24" fill="none" stroke="#101514" stroke-width="2.3" stroke-linejoin="round"><path d="M12 3l8 4.5v9L12 21l-8-4.5v-9z"/><path d="M4 7.5l8 4.5 8-4.5M12 12v9"/></svg>',
  bolt:'<svg width="20" height="20" viewBox="0 0 24 24" fill="#101514"><path d="M13 2L5 13.5h5.5L9.5 22 19 9.5h-5.8z"/></svg>'
};
/* ---------- Oberfläche ---------- */
var ui={seen:{},tab:'start',lead:null,detail:null,sheet:null,pend:{},tm:'active',tf:'all',m:null,h:{val:0},scanNext:null,confirm:null,sheetKind:'',curMat:null};
var PH_URL={};   /* lokale Fotos, die noch nicht hochgeladen sind */
var SU={};       /* signierte Foto-Adressen */

var person=function(id){
  var p=C.profiles.filter(function(x){return x.id===id})[0];
  return p?{id:p.id,name:p.name,role:p.role,ini:initials(p.name)}:{id:id,name:'Unbekannt',role:'',ini:'?'};
};
var isOffice=function(){return !!ME&&ME.role==='buero'};
var proj=function(id){return S.projects.filter(function(p){return p.id===id})[0]};
var mat=function(id){return S.mats.filter(function(m){return m.id===id})[0]};
var activeProjects=function(){return S.projects.filter(function(p){return p.status==='aktiv'})};
var openTasksOf=function(pid){return S.tasks.filter(function(t){return !t.done&&t.project===pid})};
var isLow=function(m){return m.min>0&&m.stock<m.min};
var first=function(n){return String(n||'').split(' ')[0]};
var city=function(a){var s=String(a||'').split(',');return (s[s.length-1]||'').trim()};
function fmtDate(s,time){
  if(!s)return '';
  var t=TODAY(),r;
  if(s===t)r='Heute';else if(s===dayOff(1))r='Morgen';else if(s===dayOff(-1))r='Gestern';
  else r=new Date(s+'T12:00').toLocaleDateString('de-AT',{weekday:'short',day:'numeric',month:'numeric'});
  return r+(time?', '+String(time).slice(0,5):'');
}
function fmtTs(ts){return fmtDate(iso(new Date(ts)))}
function toast(msg){
  var t=$('#toast');t.textContent=msg;t.classList.add('on');clearTimeout(toast.k);
  toast.k=setTimeout(function(){t.classList.remove('on')},3200);
}

/* ---------- Kopf, Status ---------- */
function renderHeader(){
  var a=$('#avatar');a.textContent=ME?ME.ini:'';
  $('#app').setAttribute('data-tab',ui.tab);
  document.querySelectorAll('.navb').forEach(function(b){
    if(b.dataset.tab===ui.tab)b.setAttribute('aria-current','page');else b.removeAttribute('aria-current');
  });
  setStatus();
}
function setStatus(){
  var s=$('#status');if(!s)return;
  var n=OB.length,off=!navigator.onLine;
  if(sync_.running){s.className='status busy';s.textContent='Abgleich…';return}
  if(off||sync_.err==='net'){s.className='status off';s.textContent='Offline'+(n?' · '+n+' offen':'');return}
  if(sync_.err==='auth'||sync_.err==='fail'){s.className='status off';s.textContent='Abgleich gestört'+(n?' · '+n:'');return}
  if(n){s.className='status off';s.textContent=n+' offen';return}
  s.className='status';s.textContent='Online';
}

/* ---------- Reiter ---------- */
function taskRow(t,o){
  o=o||{};
  var pn=t.project?proj(t.project):null,late=!t.done&&t.due&&t.due<TODAY();
  var sub=[];
  if(pn)sub.push('<span>'+esc(pn.label)+'</span>');
  if(t.due)sub.push('<span class="'+(late?'late':'')+'">'+esc(fmtDate(t.due,t.time))+'</span>');
  if(o.who&&t.assignee)sub.push('<span>'+esc(first(person(t.assignee).name))+'</span>');
  var pend=!!ui.pend[t.id];
  var right=o.restore?'<button class="btn small" data-act="restoreTask" data-id="'+t.id+'">Wieder aktiv</button>':'';
  var cb=o.restore?'<span class="chk" style="background:var(--tab)">'+ico.check+'</span>':'<button class="chk" data-act="chk" data-id="'+t.id+'" aria-label="Aufgabe abhaken: '+esc(t.name)+'">'+ico.check+'</button>';
  return '<div class="task'+((pend||t.done)?' is-done':'')+'" data-tid="'+t.id+'">'+cb+
    '<div class="tt"><span class="name">'+esc(t.name)+'</span><div class="sub">'+sub.join('<span aria-hidden="true">·</span>')+'</div></div>'+right+'</div>';
}
function tabAufgaben(){
  var act=S.tasks.filter(function(t){return !t.done}).sort(function(a,b){return b.created-a.created});
  var five=act.slice(0,5);
  var rows=five.length?five.map(function(t){return taskRow(t,{who:true})}).join(''):'<div class="empty"><b>Alles erledigt</b>Mit + legst du eine neue Aufgabe an.</div>';
  var nm=act.length-5,more=nm>0?'<p class="hint" style="text-align:center">'+nm+(nm===1?' weitere aktive Aufgabe':' weitere aktive Aufgaben')+' hinter den drei Punkten</p>':'';
  return '<div class="titlebar rise" style="--i:0"><div class="pill">Aufgaben</div><button class="plus" data-act="addTask" aria-label="Neue Aufgabe">+</button></div>'+
    '<div class="body"><div class="panel rise" style="--i:1">'+rows+'<button class="dots" data-act="allTasks" aria-label="Alle aktiven Aufgaben anzeigen"><span></span><span></span><span></span></button></div>'+more+'</div>';
}
function tabLager(){
  var low=S.mats.filter(isLow).sort(function(a,b){return a.stock/a.min-b.stock/b.min});
  var lowHtml=low.length?'<div class="lowbox rise" style="--i:4"><div class="sec"><span>Unter Mindestbestand</span><span class="tag red">'+low.length+'</span></div><div class="list">'+low.slice(0,3).map(function(m){
      return '<button class="item" data-act="openMat" data-id="'+m.id+'"><span class="grow"><span class="t">'+esc(m.name)+'</span><span class="s">Mindestbestand '+nf(m.min,0)+' '+esc(m.unit)+'</span></span><span class="r num" style="color:var(--red)">'+nf(m.stock,0)+' '+esc(m.unit)+'</span></button>'}).join('')+'</div></div>'
    :'<p class="hint rise" style="--i:4">'+(S.mats.length?'Alle Bestände liegen über dem Mindestbestand.':(isOffice()?'Noch kein Material im Lager. Lege mit „Material anlegen“ das erste an.':'Noch kein Material im Lager.'))+'</p>';
  return '<div class="titlebar rise" style="--i:0"><div class="pill">Lager</div><button class="plus" data-act="delivery" aria-label="Lieferung verbuchen">+</button></div>'+
    '<div class="body">'+(isOffice()?'<button class="btn main wide rise" style="--i:1" data-act="newMat">Material anlegen</button>':'')+
    '<div class="row2 rise" style="--i:2"><button class="btn" data-act="matSearch">'+ico.search+'Suchen</button><button class="btn" data-act="scan" data-next="detail">'+ico.qr+'Scannen</button></div>'+
    '<div class="rise" style="--i:3"><div class="sec" style="margin-bottom:8px">Lagerorte</div><div class="loctiles">'+LOCS.map(function(l){var n=S.mats.filter(function(m){return m.locs[l.k]>0}).length;return '<button type="button" data-act="locList" data-v="'+l.k+'" aria-label="'+l.n+': '+n+' Materialien"><span>'+l.n+'</span><b class="num">'+n+'</b></button>'}).join('')+'</div></div>'+lowHtml+'</div>';
}
function tabProjekte(){
  var soon=activeProjects().filter(function(p){return p.termin===TODAY()||p.termin===dayOff(1)}).sort(function(a,b){return a.termin<b.termin?-1:1});
  var list=soon.length?'<div class="list">'+soon.map(function(p){
      return '<button class="item" data-act="openProj" data-id="'+p.id+'"><span class="grow"><span class="t">'+esc(p.name)+'</span><span class="s">'+esc(p.addr)+'</span></span>'+(openTasksOf(p.id).length?'<span class="rd" title="Offene Aufgaben"></span>':'')+'<span class="r">'+esc(fmtDate(p.termin))+'</span></button>'}).join('')+'</div>'
    :'<p class="hint">'+(activeProjects().length?'Heute und morgen stehen keine Termine an.':(isOffice()?'Noch keine Projekte. Lege mit + das erste an.':'Noch keine Projekte angelegt.'))+'</p>';
  return '<div class="titlebar rise" style="--i:0"><div class="pill">Projekte</div>'+(isOffice()?'<button class="plus" data-act="newProj" aria-label="Neues Projekt">+</button>':'')+'</div>'+
    '<div class="body"><div class="row2 rise" style="--i:1"><button class="btn" data-act="projArchive">Archiv</button><button class="btn" data-act="projSearch">'+ico.search+'Suchen</button></div>'+
    '<div class="lowbox rise" style="--i:2"><div class="sec"><span>Heute und morgen</span></div>'+list+'</div></div>';
}
function tabHome(){
  var hr=new Date().getHours(),g=hr<11?'Guten Morgen':hr<18?'Guten Tag':'Guten Abend';
  var open=S.tasks.filter(function(t){return !t.done}),mine=open.filter(function(t){return t.assignee===ME.id}).length;
  var low=S.mats.filter(isLow).length,heute=activeProjects().filter(function(p){return p.termin===TODAY()}).length;
  function btn(tab,c,label,l1,l2,i){return '<button class="hbtn rise" style="--c:var(--'+c+');--i:'+i+'" data-act="tab" data-tab="'+tab+'"><span>'+label+'</span><small>'+l1+'<br>'+l2+'</small></button>'}
  return '<div class="home"><svg class="lg rise" style="--i:0" viewBox="0 0 3067 3610" role="img" aria-label="strom-macher Logo"><use href="#sm-logo"/></svg>'+
    '<h1 class="rise" style="--i:1">strom-macher</h1><p class="hi rise" style="--i:1">'+g+', '+esc(first(ME.name))+'</p>'+
    '<div class="hbtns">'+
    btn('aufgaben','blue','Aufgaben',open.length+' offen',mine+' für dich',2)+
    btn('lager','green','Lager',low?low+' unter Mindestbestand':'Bestand in Ordnung',S.mats.length+' Materialien',3)+
    btn('projekte','yellow','Projekte',heute+(heute===1?' Termin heute':' Termine heute'),activeProjects().length+' aktiv',4)+
    '</div></div>';
}
function renderTab(anim){
  if(!ME)return;
  $('#tabBody').classList.toggle('still',anim===false);
  if(ui.tab==='vertrieb'){
    var sg=vSig();if(anim===false&&sg===vui.sig&&$('#vmap'))return;
    var vb=$('#vbody'),vst=anim===false&&vb?vb.scrollTop:0;
    vui.sig=sg;$('#tabBody').innerHTML=tabVertrieb();mountMap();
    var nb=$('#vbody');if(nb&&vst)nb.scrollTop=vst;
    geoPending();return;
  }
  vui.sig='';
  var h=ui.tab==='start'?tabStart():ui.tab==='home'?tabHome():ui.tab==='lager'?tabLager():ui.tab==='projekte'?tabProjekte():tabAufgaben();
  $('#tabBody').innerHTML=h;
}

/* ---------- Bubbles ---------- */
var SLOTS=[[33,24,'l'],[2,3,'m'],[63,34,'l'],[64,66,'m'],[3,44,'m'],[36,63,'m'],[73,2,'s'],[40,0,'s'],[2,76,'s'],[18,64,'s']];
function bubbleProjects(){
  var t=TODAY(),tm=dayOff(1);
  function rel(p){
    var s=0,own=S.tasks.filter(function(x){return !x.done&&x.project===p.id&&x.assignee===ME.id}).length;
    if(p.termin===t)s+=3;else if(p.termin===tm)s+=2;
    if(own)s+=2;
    return s;
  }
  return activeProjects().map(function(p){return {p:p,r:rel(p)}}).sort(function(a,b){return b.r-a.r||b.p.created-a.p.created}).slice(0,10).map(function(x){return x.p});
}
function renderBubbles(){
  if(!ME)return;
  var list=bubbleProjects(),el=$('#bubbles');
  var sig=list.map(function(p){return p.id+(openTasksOf(p.id).length?'!':'')+p.label}).join('|');
  if(sig===ui.bsig)return;ui.bsig=sig;
  if(!list.length){el.innerHTML='<div class="nobub">Noch keine Projekte. Im Reiter Projekte mit + anlegen.</div>';return}
  el.innerHTML=list.map(function(p,i){
    var s=SLOTS[i],sg=(i%2?-1:1),dx=(4+(i*3)%6)*sg,dy=(5+(i*5)%5)*(i%3===0?-1:1);
    var dot=openTasksOf(p.id).length?'<i class="rd" title="Offene Aufgaben"></i>':'';
    return '<div class="bubble sz-'+s[2]+'" style="left:'+s[0]+'%;top:'+s[1]+'%;--dx:'+dx+'px;--dy:'+dy+'px;--dur:'+(5+(i%4)*.9).toFixed(1)+'s;--del:-'+(i*.8).toFixed(1)+'s">'+
      '<button class="bub" style="--i:'+i+'" data-act="openProj" data-id="'+p.id+'" aria-label="Projekt '+esc(p.name)+(dot?', offene Aufgaben':'')+'"><span>'+esc(p.label)+'</span>'+dot+'</button></div>';
  }).join('');
}

/* ---------- Projektdetail ---------- */
function hoursTotal(p){return p.hours.reduce(function(s,x){return s+x.h},0)}
function canStorno(by){return isOffice()||by===ME.id}
function renderDetail(keep){
  if(ui.lead){renderLead(keep);return}
  var d=$('#detail'),p=proj(ui.detail);d.classList.remove('ldet');d.classList.remove('flip');
  if(!p){d.hidden=true;d.innerHTML='';return}
  var old=$('.dbody',d),st=keep&&old?old.scrollTop:0;
  var arch=p.status!=='aktiv',off=isOffice();
  var tasks=openTasksOf(p.id).sort(function(a,b){return (a.due||'9')<(b.due||'9')?-1:1});
  var bks=[];
  p.hours.forEach(function(x){bks.push({t:'h',id:x.id,at:x.at,x:x})});
  p.mat.forEach(function(x){bks.push({t:'m',id:x.id,at:x.at,x:x})});
  bks.sort(function(a,b){return b.at-a.at});
  var bkHtml=bks.length?bks.slice(0,10).map(function(b){
    var del=function(t){return (arch||!canStorno(b.x.by))?'':'<button class="del" data-act="delBk" data-t="'+t+'" data-id="'+b.id+'" aria-label="Buchung stornieren">'+ico.x+'</button>'};
    if(b.t==='h')return '<div class="bk"><span class="bi h">'+ico.clock+'</span><div class="grow"><div class="t num">'+nf(b.x.h)+' h</div><div class="s">'+esc(fmtDate(b.x.date))+' · '+esc(first(person(b.x.by).name))+(b.x.note?' · '+esc(b.x.note):'')+'</div></div>'+del('h')+'</div>';
    var m=mat(b.x.matId)||{name:'Material',unit:''};
    return '<div class="bk"><span class="bi m">'+ico.box+'</span><div class="grow"><div class="t">'+esc(m.name)+'</div><div class="s num">'+nf(b.x.qty,1)+' '+esc(m.unit)+' · '+esc(locName(b.x.loc))+' · '+esc(fmtTs(b.at))+' · '+esc(first(person(b.x.by).name))+'</div></div>'+del('m')+'</div>';
  }).join(''):'<p class="hint">Noch nichts gebucht.</p>';
  var photos=p.photos.map(function(f){var u=PH_URL[f.id]||'';return '<button class="ph" data-act="viewPhoto" data-id="'+f.id+'" aria-label="Foto vom '+esc(fmtTs(f.at))+' ansehen"><img alt="" '+(u?'src="'+u+'"':'')+' data-path="'+esc(f.path)+'" data-id="'+f.id+'"></button>'}).join('');
  var addPh=arch?'':'<button class="phadd" data-act="photoCam">'+ico.cam+'Kamera</button><button class="phadd" data-act="photoGal">'+ico.img+'Galerie</button>';
  var maps='https://www.google.com/maps/search/?api=1&query='+encodeURIComponent(p.addr);
  var telh=String(p.phone||'').replace(/[^\d+]/g,''),tel2=String(p.phone2||'').replace(/[^\d+]/g,'');
  d.hidden=false;
  d.innerHTML='<div class="dhead"><button class="x" data-act="closeDetail" aria-label="Zurück">'+ico.back+'</button><h1>'+esc(p.name)+'</h1>'+(arch?'<span class="tag">Archiv</span>':'')+'</div>'+
  '<div class="dbody">'+
  (arch?'<div class="banner"><span>Dieses Projekt ist abgeschlossen. Buchen und Aufgaben sind gesperrt.</span>'+(off?'<button class="btn main small" data-act="reopenProj">Wieder öffnen</button>':'')+'</div>':'')+
  (off?'<div style="display:flex;justify-content:flex-end;margin-bottom:6px"><button class="btn small" data-act="editProj">Bearbeiten</button></div>':'')+'<div class="contact"><div class="crow"><span style="color:var(--ink2)">'+ico.pin+'</span><div class="grow"><span class="k">Adresse</span><span class="v">'+esc(p.addr||'nicht erfasst')+'</span></div>'+(p.addr?'<a href="'+maps+'" target="_blank" rel="noopener">Navigation</a>':'')+'</div>'+
  '<div class="crow"><span style="color:var(--ink2)">'+ico.tel+'</span><div class="grow"><span class="k">Telefon</span><span class="v num">'+esc(p.phone||'nicht erfasst')+'</span></div>'+(telh?'<a href="tel:'+esc(telh)+'">Anrufen</a>':'')+'</div>'+
  (p.phone2?'<div class="crow"><span style="width:22px;flex:none"></span><div class="grow"><span class="k">Telefon 2</span><span class="v num">'+esc(p.phone2)+'</span></div>'+(tel2?'<a href="tel:'+esc(tel2)+'">Anrufen</a>':'')+'</div>':'')+
  (p.email?'<div class="crow"><span style="width:22px;flex:none"></span><div class="grow"><span class="k">E-Mail</span><span class="v">'+esc(p.email)+'</span></div><a href="mailto:'+esc(p.email)+'">Schreiben</a></div>':'')+
  (p.kundennr?'<div class="crow"><span style="width:22px;flex:none"></span><div class="grow"><span class="k">Kundennummer</span><span class="v num">'+esc(p.kundennr)+'</span></div></div>':'')+
  (p.termin?'<div class="crow"><span style="width:22px;flex:none"></span><div class="grow"><span class="k">Termin</span><span class="v">'+esc(fmtDate(p.termin))+'</span></div></div>':'')+
  (p.note?'<div class="crow"><div class="grow"><span class="k">Notiz</span><span class="v">'+esc(p.note)+'</span></div></div>':'')+'</div>'+
  '<div class="sect"><div class="sec"><span>Offene Aufgaben</span>'+(arch?'':'<button class="btn small" data-act="addTask" data-pid="'+p.id+'">+ Aufgabe</button>')+'</div><div class="plain">'+(tasks.length?tasks.map(function(t){return taskRow(t,{who:true})}).join(''):'<p class="hint">Keine offenen Aufgaben.</p>')+'</div></div>'+
  '<div class="sect"><div class="sec"><span>Fotos</span><span class="num">'+p.photos.length+'</span></div><div class="photos">'+photos+addPh+'</div></div>'+
  '<div class="sect" style="border-color:var(--green)"><div class="sec"><span>Aufmaß</span></div>'+
  '<div class="figs"><div><div class="big num">'+nf(hoursTotal(p))+'<span style="font-size:22px"> h</span></div><div class="l">Stunden gesamt</div></div><div><div class="big num">'+p.mat.length+'</div><div class="l">Materialbuchungen</div></div></div>'+
  (arch?'':'<div class="row2"><button class="btn main" data-act="hours" data-pid="'+p.id+'">'+ico.clock.replace('#101514','currentColor')+'Stunden</button><button class="btn" data-act="book" data-pid="'+p.id+'">'+ico.box.replace('#101514','currentColor')+'Material</button></div>')+
  '<div>'+bkHtml+'</div>'+(bks.length?'<button class="btn wide" data-act="exportAufmass">Aufmaß als Excel (zum Drucken)</button>':'')+'</div>'+
  (off&&!arch?'<button class="btn danger wide" data-act="closeProj" data-id="'+p.id+'">Projekt abschließen</button>':'')+
  '</div>';
  var nb=$('.dbody',d);if(nb&&st)nb.scrollTop=st;
  loadPhotos();
}
function refresh(keep){renderTab(false);renderBubbles();renderHeader();if(ui.detail||ui.lead)renderDetail(keep)}
function tryPendingLead(){
  var id=ui.pendingLead;if(!id||!lead(id))return false;ui.pendingLead=null;
  setTab('vertrieb');openLead(id);return true;
}
function afterChange(){
  if(!ME)return;
  if(ui.pendingLead&&tryPendingLead())return;
  if(ui.view==='app'){
    refresh(true);
    if(ui.sheetKind==='tasksAll')sheetTasksAllKeep();
    else if(ui.sheetKind==='matDetail'&&ui.qrPending){var m=mat(ui.curMat);if(m&&m.qr)keepRender(function(){sheetMatDetail(ui.curMat)})}
  }
}

/* ---------- Sheets ---------- */
function sheetShell(title,sub,body,ox){
  return '<div class="scrim" data-act="closeSheet"></div><div class="sheet" role="dialog" aria-modal="true" aria-label="'+esc(title)+'"'+(ox?' style="--ox:'+ox+'"':'')+'><div class="shead"><div><h2>'+esc(title)+'</h2>'+(sub?'<div class="sub">'+esc(sub)+'</div>':'')+'</div><button class="x" data-act="closeSheet" aria-label="Schließen">'+ico.x+'</button></div>'+body+'</div>';
}
function openSheet(kind,html){
  stopScan();
  var L=$('#layer');L.classList.remove('closing');if(!ui.keepFx)L.classList.remove('nofx');L.innerHTML=html;ui.sheetKind=kind;
}
function closeSheet(){
  var L=$('#layer');if(!L.firstChild)return;
  stopScan();
  L.classList.remove('nofx');L.classList.add('closing');ui.sheetKind='';
  setTimeout(function(){if(ui.sheetKind==='')L.innerHTML='';L.classList.remove('closing')},170);
}
function fld(id,label,input,hint){return '<div class="fld" id="f-'+id+'"><label for="'+id+'">'+label+'</label>'+input+(hint?'<div class="hint">'+hint+'</div>':'')+'<div class="err" id="e-'+id+'"></div></div>'}
function setErr(id,msg){var f=$('#f-'+id),e=$('#e-'+id);if(!f)return;if(msg){f.classList.add('bad');e.textContent=msg;var i=$('#'+id);if(i)i.focus()}else{f.classList.remove('bad');e.textContent=''}}
function val(id){var e=$('#'+id);return e?e.value.trim():''}
function num(id){return Number(String(val(id)).replace(',','.'))}
function nz(s){s=String(s==null?'':s).trim();return s?s:null}

/* Aufgabe anlegen */
function projOptions(q,sel,max){
  q=String(q||'').toLowerCase().trim();
  var list=activeProjects();
  if(q)list=list.filter(function(p){return (p.name+' '+p.addr+' '+p.kundennr).toLowerCase().indexOf(q)>-1});
  list=list.sort(function(a,b){return a.name.localeCompare(b.name,'de')});
  var cut=list.length>max;list=list.slice(0,max);
  if(sel&&!list.some(function(p){return p.id===sel})){var sp=proj(sel);if(sp)list.unshift(sp)}
  return '<option value="">Kein Projekt</option>'+list.map(function(p){return '<option value="'+p.id+'"'+(p.id===sel?' selected':'')+'>'+esc(p.name)+' · '+esc(city(p.addr))+'</option>'}).join('')+(cut?'<option disabled>… weitere mit der Suche eingrenzen</option>':'');
}
function sheetTaskNew(pid){
  var opts=PEOPLE.map(function(p){return '<option value="'+p.id+'"'+(p.id===ME.id?' selected':'')+'>'+esc(p.name)+'</option>'}).join('');
  var big=activeProjects().length>25;
  var body='<form class="form" id="frm" data-submit="saveTask" novalidate>'+
    fld('tn','Name der Aufgabe','<input id="tn" type="text" autocomplete="off" placeholder="z. B. Zählerkasten fotografieren">')+
    fld('ta','Bearbeiter','<select id="ta">'+opts+'</select>')+
    fld('tp','Projekt',(big&&!pid?'<input id="tpq" type="search" data-filter="tp" placeholder="Projekt suchen" autocomplete="off" aria-label="Projekt suchen" style="margin-bottom:6px">':'')+'<select id="tp">'+projOptions('',pid,60)+'</select>')+
    '<div class="fld"><label for="td">Termin</label><div class="chips" style="margin-bottom:2px"><button type="button" class="chip" data-act="setDate" data-v="0">Heute</button><button type="button" class="chip" data-act="setDate" data-v="1">Morgen</button><button type="button" class="chip" data-act="setDate" data-v="7">In 7 Tagen</button><button type="button" class="chip" data-act="setDate" data-v="">Ohne</button></div>'+
    '<div class="grid2"><input id="td" type="date" aria-label="Datum"><input id="tt" type="time" aria-label="Uhrzeit"></div></div>'+
    '<button class="btn main wide" type="submit">Aufgabe anlegen</button></form>';
  openSheet('taskNew',sheetShell('Neue Aufgabe','',body,'92%'));
}
function submitTask(){
  var n=val('tn');if(!n){setErr('tn','Bitte einen Namen eingeben.');return}setErr('tn','');
  var t={id:uuid(),name:n,project_id:val('tp')||null,assignee:val('ta')||ME.id,due:val('td')||null,due_time:val('tt')||null,done:false,done_at:null,created_by:ME.id,created_at:new Date().toISOString()};
  closeSheet();mut('tasks','up',t);
  toast(t.assignee!==ME.id?'Aufgabe angelegt für '+first(person(t.assignee).name):'Aufgabe angelegt');
}

/* Alle Aufgaben (Bubble) */
function sheetTasksAll(){
  var list=S.tasks.filter(function(t){return ui.tm==='active'?!t.done:t.done});
  if(ui.tf==='mine')list=list.filter(function(t){return t.assignee===ME.id});
  list.sort(function(a,b){return ui.tm==='active'?((a.due||'9')<(b.due||'9')?-1:a.due===b.due?b.created-a.created:1):b.doneAt-a.doneAt});
  var total=list.length;if(list.length>150)list=list.slice(0,150);
  var rows=list.length?list.map(function(t){return taskRow(t,{who:true,restore:ui.tm==='archive'})}).join(''):'<div class="empty"><b>'+(ui.tm==='active'?'Nichts offen':'Archiv ist leer')+'</b>'+(ui.tm==='active'?'Alle Aufgaben in dieser Ansicht sind erledigt.':'Erledigte Aufgaben erscheinen hier.')+'</div>';
  var body='<div class="form" style="gap:12px"><div class="seg"><button data-act="tm" data-v="active" class="'+(ui.tm==='active'?'on':'')+'">Aktiv</button><button data-act="tm" data-v="archive" class="'+(ui.tm==='archive'?'on':'')+'">Archiv</button></div>'+
    '<div class="chips"><button class="chip '+(ui.tf==='all'?'on':'')+'" data-act="tf" data-v="all">Alle</button><button class="chip '+(ui.tf==='mine'?'on':'')+'" data-act="tf" data-v="mine">Meine</button></div>'+
    '<div id="tasklist">'+rows+'</div></div>';
  openSheet('tasksAll',sheetShell(ui.tm==='active'?'Aktive Aufgaben':'Archiv',total+(total===1?' Aufgabe':' Aufgaben'),body,'50%'));
}

/* Projekt anlegen */
function shortOf(n){var p=String(n).trim().split(/\s+/);return p.length>1?p.slice(1).join(' '):n}
function sheetProjNew(){sheetProjForm(null)}
function sheetProjForm(p){
  ui.editProj=p?p.id:null;
  var v=function(k){return p&&p[k]?esc(p[k]):''};
  var body='<form class="form" data-submit="saveProj" novalidate>'+
    fld('pn','Name','<input id="pn" type="text" autocomplete="off" placeholder="Vor- und Nachname des Kunden" value="'+v('name')+'">')+
    (p?fld('ps','Kurzname (Anzeige in den Bubbles)','<input id="ps" type="text" autocomplete="off" value="'+v('label')+'">'):'')+
    fld('pa','Adresse','<input id="pa" type="text" autocomplete="off" placeholder="Straße Nr., PLZ Ort" value="'+v('addr')+'">')+
    fld('pph','Telefonnummer','<input id="pph" type="tel" inputmode="tel" placeholder="+43 …" value="'+v('phone')+'">')+
    (p?fld('pph2','Telefonnummer 2 (optional)','<input id="pph2" type="tel" inputmode="tel" value="'+v('phone2')+'">'):'')+
    fld('pe','E-Mail (optional)','<input id="pe" type="email" autocomplete="off" value="'+v('email')+'">')+
    fld('pt','Termin (optional)','<input id="pt" type="date" value="'+v('termin')+'">')+
    fld('pno','Notiz (optional)','<textarea id="pno">'+v('note')+'</textarea>')+
    '<button class="btn main wide" type="submit">'+(p?'Änderungen speichern':'Projekt anlegen')+'</button></form>';
  openSheet('projNew',sheetShell(p?'Projekt bearbeiten':'Neues Projekt',p?p.name:'',body,'92%'));
}
function submitProj(){
  var ok=true;
  if(!val('pn')){setErr('pn','Bitte einen Namen eingeben.');ok=false}else setErr('pn','');
  if(!ui.editProj){
    if(!val('pa')){if(ok)setErr('pa','Bitte eine Adresse eingeben.');else{var f=$('#f-pa');f.classList.add('bad');$('#e-pa').textContent='Bitte eine Adresse eingeben.'}ok=false}else setErr('pa','');
  }
  if(!ok)return;
  var n=val('pn');
  if(ui.editProj){
    var id=ui.editProj;ui.editProj=null;
    closeSheet();
    mut('projects','up',{id:id,name:n,short:nz(val('ps'))||shortOf(n),addr:nz(val('pa')),phone:nz(val('pph')),phone2:nz(val('pph2')),email:nz(val('pe')),note:nz(val('pno')),termin:val('pt')||null});
    toast('Projekt gespeichert');return;
  }
  var p={id:uuid(),kundennr:null,name:n,short:shortOf(n),addr:val('pa'),phone:nz(val('pph')),phone2:null,email:nz(val('pe')),note:nz(val('pno')),termin:val('pt')||null,status:'aktiv',created_at:new Date().toISOString()};
  closeSheet();mut('projects','up',p);toast('Projekt „'+n+'“ angelegt');
}

/* Projektliste: Suche oder Archiv */
function projRows(q,arch){
  q=String(q||'').toLowerCase().trim();
  var list=S.projects.filter(function(p){return arch?p.status!=='aktiv':p.status==='aktiv'});
  var qd=q.replace(/[^\d]/g,'');
  if(q)list=list.filter(function(p){return (p.name+' '+p.addr+' '+p.kundennr).toLowerCase().indexOf(q)>-1||(qd.length>3&&String(p.phone).replace(/[^\d]/g,'').indexOf(qd)>-1)});
  list=list.sort(function(a,b){return q?a.name.localeCompare(b.name,'de'):b.created-a.created});
  var total=list.length;list=list.slice(0,60);
  return {total:total,html:list.map(function(p){
    var n=openTasksOf(p.id).length;
    return '<button class="item" data-act="openProj" data-id="'+p.id+'"><span class="grow"><span class="t">'+esc(p.name)+'</span><span class="s">'+esc(p.addr)+'</span></span>'+(n&&!arch?'<span class="rd" title="Offene Aufgaben"></span>':'')+'</button>';
  }).join('')+(total>60?'<p class="hint" style="padding:10px 2px">'+(total-60)+' weitere – Suche eingrenzen.</p>':'')};
}
function sheetProjList(mode){
  var arch=mode==='archive',r=projRows('',arch);
  var body='<div class="form" style="gap:10px">'+(arch?'<p class="hint">Antippen zum Ansehen. Im Projekt kannst du es wieder öffnen.</p>':'<div class="fld"><input id="q" type="search" data-filter="proj" placeholder="Name, Ort oder Kundennummer" aria-label="Projekte suchen" autocomplete="off"></div>')+'<div class="list" id="flist">'+(r.html||'<div class="empty"><b>'+(arch?'Archiv ist leer':'Noch keine Projekte')+'</b>'+(arch?'Abgeschlossene Projekte erscheinen hier.':'Lege im Reiter Projekte mit + das erste an.')+'</div>')+'</div><p class="hint" id="nores" hidden>Kein Projekt gefunden.</p></div>';
  ui.plArch=arch;
  openSheet('projList',sheetShell(arch?'Projekt-Archiv':'Projekte suchen',r.total+' Projekte',body,'30%'));
  if(!arch)setTimeout(function(){var q=$('#q');if(q&&matchMedia('(hover:hover)').matches)q.focus()},260);
}

/* Material: Suche */
function matRow(m,act,lk){
  var qn=lk?m.locs[lk]:m.stock;
  return '<button class="item" data-act="'+act+'" data-id="'+m.id+'" data-q="'+esc((m.name+' '+m.artnr+' '+m.supplier+' '+m.qr).toLowerCase())+'"><span class="grow"><span class="t">'+esc(m.name)+'</span><span class="s">'+esc(m.qr||'QR folgt')+(isOffice()&&m.supplier?' · '+esc(m.supplier):'')+'</span></span>'+(isLow(m)?'<span class="rd" title="Unter Mindestbestand"></span>':'')+'<span class="r num">'+nf(qn,0)+' '+esc(m.unit)+'</span></button>';
}
function sheetLocList(k){
  var ms=S.mats.filter(function(m){return m.locs[k]>0}).sort(function(a,b){return a.name.localeCompare(b.name,'de')});
  var body='<div class="form" style="gap:10px">'+(ms.length?'<div class="fld"><input id="q" type="search" data-filter="1" placeholder="Material suchen" aria-label="Material suchen" autocomplete="off"></div><div class="list" id="flist">'+ms.map(function(m){return matRow(m,'openMat',k)}).join('')+'</div><p class="hint" id="nores" hidden>Kein Material gefunden.</p>':'<div class="empty"><b>'+esc(locName(k))+' ist leer</b>Über „Umbuchen“ im Material oder eine Lieferung kommt Bestand hierher.</div>')+'</div>';
  openSheet('locList',sheetShell(locName(k),ms.length+' '+(ms.length===1?'Material':'Materialien')+' mit Bestand',body,'30%'));
}
/* Lagerort-Auswahl (2x2) */
function lastLoc(){try{var v=localStorage.getItem('sm-loc');if(LOCK.indexOf(v)>=0)return v}catch(e){}return 'haupt'}
function setLastLoc(k){try{localStorage.setItem('sm-loc',k)}catch(e){}}
function locSeg(g,sel,mt){
  return '<div class="locseg" role="group">'+LOCS.map(function(l){var on=l.k===sel;return '<button type="button" class="'+(on?'on':'')+'" aria-pressed="'+on+'" data-act="locPick" data-g="'+g+'" data-v="'+l.k+'"><b>'+l.n+'</b>'+(mt?'<span class="num">'+nf(mt.locs[l.k],1)+' '+esc(mt.unit)+'</span>':'')+'</button>'}).join('')+'</div>';
}
function bestLoc(mt,pref){
  if(mt.locs[pref]>0)return pref;
  for(var i=0;i<LOCK.length;i++)if(mt.locs[LOCK[i]]>0)return LOCK[i];
  return pref;
}
function sheetMatList(){
  var rows=S.mats.slice().sort(function(a,b){return a.name.localeCompare(b.name,'de')}).map(function(m){return matRow(m,'openMat')}).join('');
  var body='<div class="form" style="gap:10px"><div class="fld"><input id="q" type="search" data-filter="1" placeholder="Material suchen" aria-label="Material suchen" autocomplete="off"></div><div class="list" id="flist">'+rows+'</div><p class="hint" id="nores" hidden>Kein Material gefunden.</p>'+(S.mats.length?'':'<div class="empty"><b>Noch kein Material</b>Lege es im Reiter Lager mit „Material anlegen“ an.</div>')+'</div>';
  openSheet('matList',sheetShell('Material suchen',S.mats.length+' Materialien im Lager',body,'30%'));
  setTimeout(function(){var q=$('#q');if(q&&matchMedia('(hover:hover)').matches)q.focus()},260);
}

/* Material anlegen */
function sheetMatNew(){
  var units=['Stk','m','Rolle','Paar','Set','kg'].map(function(u){return '<option>'+u+'</option>'}).join('');
  var body='<form class="form" data-submit="saveMat" novalidate>'+
    fld('mn','Name','<input id="mn" type="text" autocomplete="off" placeholder="z. B. Montageschiene 4,2 m">')+
    '<div class="grid2">'+fld('mu','Einheit','<select id="mu">'+units+'</select>')+fld('ms','Bestand jetzt','<input id="ms" type="text" inputmode="decimal" value="0">')+'</div>'+
    '<div class="grid2">'+fld('mm','Mindestbestand','<input id="mm" type="text" inputmode="decimal" placeholder="optional">')+fld('mpr','Einkaufspreis (€)','<input id="mpr" type="text" inputmode="decimal" placeholder="optional">')+'</div>'+
    fld('msu','Lieferant','<input id="msu" type="text" autocomplete="off" placeholder="optional">')+
    fld('mar','Artikelnummer des Lieferanten','<input id="mar" type="text" autocomplete="off" placeholder="optional">')+
    fld('mno','Notizen','<textarea id="mno"></textarea>')+
    '<button class="btn main wide" type="submit">Material anlegen</button></form>';
  openSheet('matNew',sheetShell('Material anlegen','Neu in der Lagerdatenbank',body,'50%'));
}
function submitMatNew(){
  if(!val('mn')){setErr('mn','Bitte einen Namen eingeben.');return}setErr('mn','');
  var st=num('ms');if(isNaN(st)||st<0){setErr('ms','Bitte eine Zahl ab 0 eingeben.');return}setErr('ms','');
  var id=uuid(),now=new Date().toISOString();
  mut('materials','up',{id:id,name:val('mn'),unit:val('mu')||'Stk',min_stock:num('mm')||0,note:nz(val('mno'))});
  mut('material_costs','up',{material_id:id,price:num('mpr')||null,supplier:nz(val('msu')),artnr:nz(val('mar'))});
  if(st>0)mut('stock_moves','up',{id:uuid(),material_id:id,project_id:null,qty:st,kind:'anfang',loc:'haupt',note:null,created_by:ME.id,created_at:now});
  toast('Material angelegt');sheetMatDetail(id,true);
}

/* Material-Detail */
function bookingsOfMat(id){
  var out=[];S.projects.forEach(function(p){p.mat.forEach(function(b){if(b.matId===id)out.push({p:p,b:b})})});
  return out.sort(function(a,b){return b.b.at-a.b.at});
}
function sheetMatDetail(id,justNew){
  var m=mat(id);if(!m)return;var off=isOffice(),low=isLow(m);ui.curMat=id;ui.qrPending=!m.qr;
  var ratio=m.min?Math.min(1,m.stock/(m.min*2)):1;
  var dels=m.deliveries.slice(0,4).map(function(d){return '<div class="bk" style="min-height:50px"><div class="grow"><div class="t num">+'+nf(d.qty,1)+' '+esc(m.unit)+' · '+esc(locName(d.loc))+'</div><div class="s">'+esc(fmtDate(d.date))+(off&&d.supplier?' · '+esc(d.supplier):'')+(d.note?' · '+esc(d.note):'')+'</div></div></div>'}).join('')||'<p class="hint">Noch keine Lieferung erfasst.</p>';
  var bks=bookingsOfMat(id).slice(0,4).map(function(x){return '<div class="bk" style="min-height:50px"><div class="grow"><div class="t num">−'+nf(x.b.qty,1)+' '+esc(m.unit)+' · '+esc(x.p.name)+'</div><div class="s">'+esc(fmtTs(x.b.at))+' · aus '+esc(locName(x.b.loc))+'</div></div></div>'}).join('')||'<p class="hint">Noch auf kein Projekt gebucht.</p>';
  var trs=transferPairs(m).slice(0,4).map(function(t){return '<div class="bk" style="min-height:50px"><div class="grow"><div class="t num">'+nf(t.qty,1)+' '+esc(m.unit)+' · '+esc(locName(t.from))+' → '+esc(locName(t.to))+'</div><div class="s">'+esc(fmtTs(t.at))+' · '+esc(first(person(t.by).name))+'</div></div>'+(canStorno(t.by)?'<button class="del" data-act="delTr" data-ids="'+t.ids.join(',')+'" data-id="'+m.id+'" aria-label="Umbuchung stornieren">'+ico.x+'</button>':'')+'</div>'}).join('');
  var locTiles='<div class="loctiles">'+LOCS.map(function(l){var v=m.locs[l.k];return '<button type="button" data-act="locList" data-v="'+l.k+'"'+(v?'':' class="zero"')+'><span>'+l.n+'</span><b class="num">'+nf(v,1)+'</b></button>'}).join('')+'</div>';
  var fields=(off?
    '<div class="grid2">'+fld('mu2','Einheit','<input id="mu2" value="'+esc(m.unit)+'">')+fld('mm2','Mindestbestand','<input id="mm2" inputmode="decimal" value="'+esc(String(m.min).replace('.',','))+'">')+'</div>'+
    '<div class="grid2">'+fld('mpr2','Einkaufspreis (€)','<input id="mpr2" inputmode="decimal" value="'+esc(String(m.price||'').replace('.',','))+'">')+fld('mar2','Artikelnr.','<input id="mar2" value="'+esc(m.artnr)+'">')+'</div>'+
    fld('msu2','Lieferant','<input id="msu2" value="'+esc(m.supplier)+'">'):'')+
    fld('mno2','Notiz','<textarea id="mno2" placeholder="Kurze Notiz für das Team">'+esc(m.note)+'</textarea>');
  var body='<div class="form" style="gap:16px"><div><div class="big num" style="color:'+(low?'var(--red)':'var(--ink)')+'">'+nf(m.stock,1)+'<span style="font-size:22px"> '+esc(m.unit)+'</span></div><div class="hint" style="margin:6px 0 8px">'+(m.min?'Mindestbestand '+nf(m.min,1)+' '+esc(m.unit)+(low?' · unterschritten':''):'Kein Mindestbestand festgelegt')+'</div><div class="bar'+(low?' low':'')+'"><i style="transform:scaleX('+ratio.toFixed(3)+')"></i></div></div>'+locTiles+
    '<div class="row2"><button class="btn main" data-act="delivery" data-id="'+m.id+'">+ Lieferung</button><button class="btn" data-act="transfer" data-id="'+m.id+'">Umbuchen</button></div>'+
    '<button class="btn wide" data-act="qr" data-id="'+m.id+'">'+ico.qr+'QR-Code</button>'+
    '<form class="form" data-submit="saveMatEdit" data-id="'+m.id+'" novalidate>'+fields+'<button class="btn wide" type="submit">'+(off?'Änderungen speichern':'Notiz speichern')+'</button></form>'+
    '<div><div class="sec" style="margin-bottom:4px">Letzte Lieferungen</div>'+dels+'</div><div><div class="sec" style="margin-bottom:4px">Letzte Buchungen auf Projekte</div>'+bks+'</div>'+(trs?'<div><div class="sec" style="margin-bottom:4px">Letzte Umbuchungen</div>'+trs+'</div>':'')+'</div>';
  openSheet('matDetail',sheetShell(m.name,(m.qr||'QR folgt')+(off&&m.supplier?' · '+m.supplier:''),body,'50%'));
}
function transferPairs(m){
  var by={},out=[];
  m.transfers.forEach(function(t){var k=t.at+'|'+t.by;(by[k]=by[k]||[]).push(t)});
  Object.keys(by).forEach(function(k){
    var g=by[k],neg=g.filter(function(t){return t.qty<0}),pos=g.filter(function(t){return t.qty>0});
    neg.forEach(function(n){
      var i=-1;for(var j=0;j<pos.length;j++)if(Math.abs(pos[j].qty+n.qty)<1e-9){i=j;break}
      var p=i>=0?pos.splice(i,1)[0]:null;
      out.push({at:n.at,by:n.by,qty:-n.qty,from:n.loc,to:p?p.loc:n.loc,ids:p?[n.id,p.id]:[n.id]});
    });
    pos.forEach(function(p){out.push({at:p.at,by:p.by,qty:p.qty,from:p.loc,to:p.loc,ids:[p.id]})});
  });
  return out.sort(function(a,b){return b.at-a.at});
}
function submitMatEdit(id){
  var m=mat(id);if(!m)return;
  if(isOffice()){
    mut('materials','up',{id:id,unit:val('mu2')||m.unit,min_stock:num('mm2')||0,note:nz(val('mno2'))});
    mut('material_costs','up',{material_id:id,price:num('mpr2')||null,supplier:nz(val('msu2')),artnr:nz(val('mar2'))});
  }else mutRpc('set_material_note',{p_id:id,p_note:val('mno2')});
  toast('Gespeichert');sheetMatDetail(id);
}

/* Material buchen / Lieferung */
function matUse(){
  var cnt={};S.projects.forEach(function(p){p.mat.forEach(function(b){cnt[b.matId]=(cnt[b.matId]||0)+1})});
  return S.mats.slice().sort(function(a,b){return (cnt[b.id]||0)-(cnt[a.id]||0)});
}
function sheetMat(){
  var m=ui.m,mt=m.sel&&mat(m.sel),book=m.mode==='book',p=m.pid&&proj(m.pid);
  if(mt&&!m.loc)m.loc=book?bestLoc(mt,lastLoc()):'haupt';
  var title=book?'Material buchen':'Lieferung verbuchen',sub=book&&p?'auf Projekt '+p.name:'Bestand erhöhen';
  var body;
  if(!mt){
    var favs=matUse().slice(0,4).map(function(x){return '<button class="chip" data-act="pickMat" data-id="'+x.id+'">'+esc(x.name.split(',')[0])+'</button>'}).join('');
    var rows=S.mats.slice().sort(function(a,b){return a.name.localeCompare(b.name,'de')}).map(function(x){return matRow(x,'pickMat')}).join('');
    body='<div class="form" style="gap:12px"><button class="btn main wide" data-act="scan" data-next="'+(book?'book':'deliver')+'">'+ico.qr+'QR-Code scannen</button>'+
      (book&&S.mats.length?'<div><div class="sec" style="margin-bottom:8px">Zuletzt verwendet</div><div class="chips">'+favs+'</div></div>':'')+
      '<div class="fld"><input id="q" type="search" data-filter="1" placeholder="Material suchen" aria-label="Material suchen" autocomplete="off"></div><div class="list" id="flist">'+rows+'</div><p class="hint" id="nores" hidden>Kein Material gefunden.</p>'+(S.mats.length?'':'<div class="empty"><b>Noch kein Material</b>Lege es im Reiter Lager an.</div>')+'</div>';
  }else{
    var chips=(mt.unit==='m'?[10,50,100]:[1,5,10]).map(function(n){return '<button type="button" class="chip" data-act="qtyAdd" data-v="'+n+'">+'+n+'</button>'}).join('');
    body='<form class="form" data-submit="'+(book?'saveBook':'saveDelivery')+'" novalidate>'+
      '<div class="banner" style="flex-direction:row;align-items:center;justify-content:space-between"><div style="min-width:0"><b style="font-family:var(--f-display)">'+esc(mt.name)+'</b><div class="hint num">Bestand gesamt '+nf(mt.stock,1)+' '+esc(mt.unit)+'</div></div><button type="button" class="btn small" data-act="unpick">Ändern</button></div>'+
      '<div class="fld" id="f-loc"><label>'+(book?'Entnommen aus':'Eingelagert in')+'</label>'+locSeg('loc',m.loc,mt)+'<div class="err" id="e-loc"></div></div>'+
      '<div class="fld" id="f-qty"><label for="qty">Menge ('+esc(mt.unit)+')</label><div class="stepper"><button type="button" class="btn" data-act="qtyStep" data-v="-1" aria-label="Weniger">−</button><input id="qty" type="text" inputmode="decimal" value="'+esc(String(m.qty).replace('.',','))+'"><button type="button" class="btn" data-act="qtyStep" data-v="1" aria-label="Mehr">+</button></div><div class="chips">'+chips+'</div><div class="err" id="e-qty"></div></div>'+
      (book?'':(isOffice()?fld('dsu','Lieferant','<input id="dsu" value="'+esc(mt.supplier)+'">'):'')+fld('dno','Lieferschein (optional)','<input id="dno" autocomplete="off">'))+
      '<button class="btn main wide" type="submit">'+(book?'Auf Projekt buchen':'Lieferung einbuchen')+'</button></form>';
  }
  openSheet('mat',sheetShell(title,sub,body,'50%'));
}
function openMatFlow(mode,pid,sel){ui.m={mode:mode,pid:pid||null,sel:sel||null,qty:1,loc:null};sheetMat()}
function submitBook(){
  var mt=mat(ui.m.sel),p=proj(ui.m.pid),q=num('qty');
  if(!(q>0)){setErr('qty','Bitte eine Menge über 0 eingeben.');return}
  var lo=ui.m.loc||'haupt',have=mt.locs[lo]||0;
  if(q>have){setErr('qty',have>0?'Im Lagerort '+locName(lo)+' sind nur '+nf(have,1)+' '+mt.unit+'.':'Im Lagerort '+locName(lo)+' ist nichts davon. Anderen Lagerort wählen.');return}
  var was=isLow(mt);
  closeSheet();setLastLoc(lo);
  mut('stock_moves','up',{id:uuid(),material_id:mt.id,project_id:p.id,qty:-q,kind:'buchung',loc:lo,note:null,created_by:ME.id,created_at:new Date().toISOString()});
  toast(nf(q,1)+' '+mt.unit+' '+mt.name.split(',')[0]+' aus '+locName(lo)+' gebucht'+(!was&&isLow(mat(mt.id))?' · Mindestbestand unterschritten':''));
}
function submitDelivery(){
  var mt=mat(ui.m.sel),q=num('qty');
  if(!(q>0)){setErr('qty','Bitte eine Menge über 0 eingeben.');return}
  var sup=isOffice()&&$('#dsu')?val('dsu'):'';
  var mid=uuid();
  closeSheet();
  var lo=ui.m.loc||'haupt';
  mut('stock_moves','up',{id:mid,material_id:mt.id,project_id:null,qty:q,kind:'lieferung',loc:lo,note:nz(val('dno')),created_by:ME.id,created_at:new Date().toISOString()});
  if(isOffice()&&sup){
    mut('delivery_suppliers','up',{move_id:mid,supplier:sup});
    if(sup!==mt.supplier)mut('material_costs','up',{material_id:mt.id,supplier:sup});
  }
  toast('+'+nf(q,1)+' '+mt.unit+' eingebucht ('+locName(lo)+') · Bestand '+nf(mat(mt.id).stock,1));
}

/* Umbuchen zwischen Lagerorten */
function sheetTransfer(id){
  var mt=mat(id);if(!mt)return;
  var from=bestLoc(mt,'haupt'),to=lastLoc();if(to===from)to=from==='haupt'?'gross':'haupt';
  ui.m={mode:'tr',sel:id,loc:from,to:to,qty:1};
  var body='<form class="form" data-submit="saveTransfer" novalidate>'+
    '<div class="fld" id="f-loc"><label>Von</label>'+locSeg('loc',from,mt)+'<div class="err" id="e-loc"></div></div>'+
    '<div class="fld" id="f-to"><label>Nach</label>'+locSeg('to',to,mt)+'<div class="err" id="e-to"></div></div>'+
    '<div class="fld" id="f-qty"><label for="qty">Menge ('+esc(mt.unit)+')</label><div class="stepper"><button type="button" class="btn" data-act="qtyStep" data-v="-1" aria-label="Weniger">−</button><input id="qty" type="text" inputmode="decimal" value="1"><button type="button" class="btn" data-act="qtyStep" data-v="1" aria-label="Mehr">+</button></div><div class="chips">'+(mt.unit==='m'?[10,50,100]:[1,5,10]).map(function(n){return '<button type="button" class="chip" data-act="qtyAdd" data-v="'+n+'">+'+n+'</button>'}).join('')+'<button type="button" class="chip" data-act="qtyAll">Alles</button></div><div class="err" id="e-qty"></div></div>'+
    '<button class="btn main wide" type="submit">Umbuchen</button></form>';
  openSheet('transfer',sheetShell('Umbuchen',mt.name,body,'50%'));
}
function submitTransfer(){
  var mt=mat(ui.m.sel),q=num('qty'),a=ui.m.loc,b=ui.m.to;if(!mt)return;
  if(a===b){setErr('to','Bitte einen anderen Lagerort als bei „Von“ wählen.');return}setErr('to','');
  if(!(q>0)){setErr('qty','Bitte eine Menge über 0 eingeben.');return}
  var have=mt.locs[a]||0;
  if(q>have){setErr('qty',have>0?'Im Lagerort '+locName(a)+' sind nur '+nf(have,1)+' '+mt.unit+'.':'Im Lagerort '+locName(a)+' ist nichts davon.');return}
  var now=new Date().toISOString();setLastLoc(b);
  mut('stock_moves','up',{id:uuid(),material_id:mt.id,project_id:null,qty:-q,kind:'umbuchung',loc:a,note:null,created_by:ME.id,created_at:now});
  mut('stock_moves','up',{id:uuid(),material_id:mt.id,project_id:null,qty:q,kind:'umbuchung',loc:b,note:null,created_by:ME.id,created_at:now});
  toast(nf(q,1)+' '+mt.unit+' von '+locName(a)+' nach '+locName(b)+' umgebucht');
  sheetMatDetail(mt.id);
}

/* Stunden */
function sheetHours(pid){
  ui.h={val:0,pid:pid};var p=proj(pid);
  var body='<form class="form" data-submit="saveHours" novalidate>'+
    '<div style="text-align:center"><div class="big num" id="hv">0<span style="font-size:24px"> h</span></div><div class="hint" id="hs">Gesamtstunden der Monteure heute</div></div>'+
    '<div class="chips" style="justify-content:center">'+[0.5,1,4,8].map(function(n){return '<button type="button" class="chip" data-act="hAdd" data-v="'+n+'">+'+nf(n)+' h</button>'}).join('')+'</div>'+
    '<div class="row2"><button type="button" class="btn small" data-act="hAdd" data-v="-0.5">− 0,5 h</button><button type="button" class="btn small" data-act="hReset">Zurücksetzen</button></div>'+
    fld('hd','Datum','<input id="hd" type="date" value="'+TODAY()+'">')+
    fld('hn','Notiz (optional)','<input id="hn" autocomplete="off" placeholder="z. B. Dachmontage, 2 Monteure">')+
    '<button class="btn main wide" id="hb" type="submit" disabled>Stunden buchen</button></form>';
  openSheet('hours',sheetShell('Stunden verbuchen','Projekt '+p.name,body,'30%'));
}
function hUpd(){
  var v=Math.max(0,ui.h.val);ui.h.val=v;
  $('#hv').innerHTML=nf(v)+'<span style="font-size:24px"> h</span>';
  var b=$('#hb');b.disabled=!(v>0);b.textContent=v>0?'Stunden buchen · '+nf(v)+' h':'Stunden buchen';
}
function submitHours(){
  if(!(ui.h.val>0))return;
  var p=proj(ui.h.pid),d=val('hd')||TODAY(),h=ui.h.val;
  closeSheet();
  mut('hours','up',{id:uuid(),project_id:p.id,work_date:d,h:h,note:nz(val('hn')),created_by:ME.id,created_at:new Date().toISOString()});
  toast(nf(h)+' h auf '+p.name+' gebucht');
}
/* ---------- Skripte nachladen ---------- */
var loaded={};
function loadScript(src){
  if(loaded[src])return loaded[src];
  loaded[src]=new Promise(function(res,rej){var s=document.createElement('script');s.src=src;s.onload=res;s.onerror=function(){delete loaded[src];rej(new Error('Skript nicht ladbar: '+src))};document.head.appendChild(s)});
  return loaded[src];
}
var isIOS=/iPhone|iPad|iPod/.test(navigator.userAgent)||(navigator.platform==='MacIntel'&&navigator.maxTouchPoints>1);
var standalone=(window.matchMedia&&matchMedia('(display-mode: standalone)').matches)||navigator.standalone===true;
function saveFile(blob,name,type){
  var f=null;try{f=new File([blob],name,{type:type})}catch(e){}
  if(isIOS&&f&&navigator.canShare&&navigator.canShare({files:[f]})){
    navigator.share({files:[f]}).catch(function(e){
      if(e&&e.name==='AbortError')return;
      /* Safari verlangt manchmal einen frischen Fingertipp – dann eigenen Knopf anbieten */
      ui.shareFile=f;
      openSheet('share',sheetShell('Datei ist fertig',name,'<div class="form"><button class="btn main wide" data-act="shareFile">Teilen / In Dateien sichern</button></div>','50%'));
    });return}
  var a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download=name;document.body.appendChild(a);a.click();
  setTimeout(function(){URL.revokeObjectURL(a.href);a.remove()},5000);
}

/* ---------- QR scannen ---------- */
var scanner=null;
function stopScan(){
  if(scanner){var s=scanner;scanner=null;try{s.stop().then(function(){try{s.clear()}catch(e){}}).catch(function(){})}catch(e){}}
}
function codeToMat(txt){
  var t=String(txt||'').trim().toUpperCase().replace(/^SM-MAT:/,'');
  if(/^\d{1,4}$/.test(t))t='SM-'+t.padStart(4,'0');
  return S.mats.filter(function(m){return m.qr&&m.qr.toUpperCase()===t})[0];
}
function sheetScan(next){
  ui.scanNext=next;
  var body='<div class="form" style="gap:12px"><div id="reader" class="reader"><p class="hint" id="rdmsg">Kamera wird gestartet…</p></div>'+
    '<form class="form" data-submit="scanManual" novalidate style="gap:10px"><div class="fld" id="f-code"><label for="code">Oder Code eintippen</label><input id="code" type="text" autocomplete="off" autocapitalize="characters" placeholder="z. B. SM-0007"><div class="err" id="e-code"></div></div><button class="btn wide" type="submit">Code suchen</button></form></div>';
  openSheet('scan',sheetShell('QR-Code scannen','',body,'50%'));
  startScan();
}
async function startScan(){
  var msg=function(t){var e=$('#rdmsg');if(e)e.textContent=t};
  try{
    await loadScript('vendor/html5-qrcode.min.js');
    if(ui.sheetKind!=='scan')return;
    var sc=new Html5Qrcode('reader',{verbose:false});
    scanner=sc;
    await sc.start({facingMode:'environment'},{fps:10,qrbox:function(w,h){var s=Math.floor(Math.min(w,h)*.8);return {width:s,height:s}}},function(txt){
      var m=codeToMat(txt);
      if(m){stopScan();scanned(m.id)}else{toast('Code nicht im Lager gefunden')}
    },function(){});
    msg('');
  }catch(e){
    scanner=null;
    msg('Die Kamera ist nicht verfügbar. Erlaube den Kamerazugriff in den Einstellungen oder tippe den Code ein.');
  }
}
function scanned(id){
  var n=ui.scanNext;
  if(n==='book'||n==='deliver'){ui.m=ui.m||{mode:n,pid:null,qty:1};ui.m.sel=id;ui.m.qty=1;sheetMat()}
  else sheetMatDetail(id);
}
function submitScanManual(){
  var m=codeToMat(val('code'));
  if(!m){setErr('code','Diesen Code gibt es nicht.');return}
  stopScan();scanned(m.id);
}

/* ---------- QR-Etikett ---------- */
function drawLabel(m){
  var W=720,Hh=900,c=document.createElement('canvas');c.width=W;c.height=Hh;var x=c.getContext('2d');
  x.fillStyle='#fff';x.fillRect(0,0,W,Hh);
  x.fillStyle='#81DD90';x.fillRect(0,0,W,22);
  var q=qrcode(0,'M');q.addData('SM-MAT:'+m.qr);q.make();
  var n=q.getModuleCount(),size=520,cell=Math.floor(size/n),qs=cell*n,ox=(W-qs)/2,oy=70;
  x.fillStyle='#141A19';
  for(var r=0;r<n;r++)for(var k=0;k<n;k++)if(q.isDark(r,k))x.fillRect(ox+k*cell,oy+r*cell,cell,cell);
  x.textAlign='center';x.fillStyle='#141A19';
  x.font='600 44px Outfit, system-ui, sans-serif';
  var words=m.name.split(' '),lines=[],cur='';
  words.forEach(function(w){var t=cur?cur+' '+w:w;if(x.measureText(t).width>620&&cur){lines.push(cur);cur=w}else cur=t});lines.push(cur);
  lines.slice(0,3).forEach(function(l,i){x.fillText(l,W/2,oy+qs+70+i*54)});
  x.font='500 32px "IBM Plex Sans", system-ui, sans-serif';x.fillStyle='#55615F';
  x.fillText(m.qr+'  ·  '+m.unit,W/2,Hh-70);
  x.font='600 26px Outfit, system-ui, sans-serif';x.fillText('strom-macher',W/2,Hh-28);
  return c;
}
function sheetQR(id){
  var m=mat(id);if(!m)return;
  if(!m.qr){toast('Der QR-Code wird vergeben, sobald die Verbindung steht.');return}
  var go=function(){
    var c=drawLabel(m);ui.qrCanvas=c;
    var body='<div class="form" style="gap:14px"><img class="qrimg" alt="QR-Etikett für '+esc(m.name)+'" src="'+c.toDataURL('image/png')+'">'+
      '<div class="row2"><button class="btn main" data-act="saveQr" data-id="'+m.id+'">Als PNG speichern</button><button class="btn" data-act="openMat" data-id="'+m.id+'">Zurück</button></div>'+
      '<p class="hint">Danach per AirDrop oder E-Mail an den Computer schicken und ausdrucken.</p></div>';
    openSheet('qr',sheetShell('QR-Code','Etikett für '+m.name,body,'50%'));
  };
  loadScript('vendor/qrcode.js').then(function(){
    if(document.fonts&&document.fonts.load){Promise.all([document.fonts.load('600 44px Outfit'),document.fonts.load('500 32px "IBM Plex Sans"')]).then(go,go)}else go();
  }).catch(function(){openSheet('qr',sheetShell('QR-Code','','<p class="hint">Der QR-Generator konnte nicht geladen werden.</p>'))});
}
function saveQr(id){
  var m=mat(id);if(!m||!ui.qrCanvas)return;
  ui.qrCanvas.toBlob(function(b){saveFile(b,'QR-'+m.qr+'.png','image/png')},'image/png');
}

/* ---------- Fotos ---------- */
function compress(file){
  return new Promise(function(res,rej){
    var url=URL.createObjectURL(file),im=new Image();
    im.onload=function(){
      var m=1600,k=Math.min(1,m/Math.max(im.width,im.height)),c=document.createElement('canvas');
      c.width=Math.round(im.width*k);c.height=Math.round(im.height*k);
      c.getContext('2d').drawImage(im,0,0,c.width,c.height);
      c.toBlob(function(b){URL.revokeObjectURL(url);b?res(b):rej(new Error('leer'))},'image/jpeg',.8);
    };
    im.onerror=function(){URL.revokeObjectURL(url);rej(new Error('Bild nicht lesbar'))};
    im.src=url;
  });
}
async function onPhoto(e){
  var files=[].slice.call(e.target.files||[]),p=proj(ui.detail);e.target.value='';
  if(!p||!files.length)return;
  var n=0;
  for(var i=0;i<files.length;i++){
    try{
      var b=await compress(files[i]),id=uuid();
      await idb.set('blob:'+id,b);
      PH_URL[id]=URL.createObjectURL(b);
      mut('photos','photo',{id:id,project_id:p.id,path:'projects/'+p.id+'/'+id+'.jpg',taken_at:new Date().toISOString(),created_by:ME.id});
      n++;
    }catch(err){toast('Das Foto konnte nicht gelesen werden.')}
  }
  if(n)toast(n+(n>1?' Fotos hinzugefügt':' Foto hinzugefügt')+(navigator.onLine?'':' · lädt später hoch'));
}
async function signedUrls(paths){
  var now=Date.now(),need=paths.filter(function(p){return !SU[p]||SU[p].exp<now});
  if(need.length&&sb&&navigator.onLine){
    try{
      var r=await sb.storage.from('photos').createSignedUrls(need,3600);
      if(r.data)r.data.forEach(function(x){if(x.signedUrl)SU[x.path]={url:x.signedUrl,exp:now+3300*1000}});
    }catch(e){}
  }
  return paths.map(function(p){return SU[p]&&SU[p].url||''});
}
async function loadPhotos(root){
  root=root||$('#detail');if(!root)return;
  var imgs=[].slice.call(root.querySelectorAll('img[data-path]')).filter(function(i){return !i.getAttribute('src')});
  if(!imgs.length)return;
  var urls=await signedUrls(imgs.map(function(i){return i.dataset.path}));
  imgs.forEach(function(im,k){
    var u=PH_URL[im.dataset.id]||urls[k];
    if(u){im.src=u;im.onerror=function(){im.removeAttribute('src')}}
  });
}
function sheetPhoto(id){
  var p=proj(ui.detail),f=p&&p.photos.filter(function(x){return x.id===id})[0];if(!f)return;
  var u=PH_URL[id]||'',who=person(f.by).name;
  var can=isOffice()&&p.status==='aktiv';
  var body='<div class="form" style="gap:12px"><img class="bigimg" alt="Foto" data-path="'+esc(f.path)+'" data-id="'+id+'" '+(u?'src="'+u+'"':'')+'><div class="hint">'+esc(fmtTs(f.at))+' · '+esc(who)+'</div>'+(can?'<button class="btn danger wide" data-act="delPhoto" data-id="'+id+'">'+(ui.confirm==='dp'+id?'Wirklich löschen?':'Foto löschen')+'</button>':'')+'</div>';
  openSheet('photo',sheetShell('Foto','',body,'50%'));
  loadPhotos($('#layer'));
}

/* ---------- Excel-Export ---------- */
async function exportXlsx(){
  try{await loadScript('vendor/xlsx.full.min.js')}catch(e){toast('Der Excel-Export konnte nicht geladen werden. Bitte einmal online öffnen.');return}
  var wb=XLSX.utils.book_new();
  var dt=function(ms){return ms?new Date(ms):''};
  var pn=function(id){var p=proj(id);return p?p.name:''},pk=function(id){var p=proj(id);return p?p.kundennr:''};
  function sheet(name,head,rows,widths){
    var ws=XLSX.utils.aoa_to_sheet([head].concat(rows),{cellDates:true});
    ws['!cols']=widths.map(function(w){return {wch:w}});
    XLSX.utils.book_append_sheet(wb,ws,name);
  }
  sheet('Projekte',['Kundennr.','Name','Adresse','Telefon','Telefon 2','E-Mail','Status','Termin','Offene Aufgaben','Stunden gesamt','Materialbuchungen','Fotos','Angelegt am','Notiz'],
    S.projects.slice().sort(function(a,b){return a.name.localeCompare(b.name,'de')}).map(function(p){
      return [p.kundennr,p.name,p.addr,p.phone,p.phone2,p.email,p.status==='aktiv'?'Aktiv':'Archiv',p.termin?new Date(p.termin+'T12:00'):'',openTasksOf(p.id).length,hoursTotal(p),p.mat.length,p.photos.length,dt(p.created),p.note];
    }),[11,28,36,18,18,28,9,12,10,10,12,7,12,30]);
  var hrows=[];
  S.projects.forEach(function(p){p.hours.forEach(function(h){hrows.push([new Date(h.date+'T12:00'),p.name,p.kundennr,h.h,h.note,person(h.by).name,dt(h.at)])})});
  hrows.sort(function(a,b){return b[0]-a[0]});
  sheet('Stunden',['Datum','Projekt','Kundennr.','Stunden','Notiz','Gebucht von','Gebucht am'],hrows,[12,28,11,9,32,18,14]);
  var mrows=[];
  S.projects.forEach(function(p){p.mat.forEach(function(b){
    var m=mat(b.matId)||{name:'',qr:'',unit:'',price:0};
    mrows.push([dt(b.at),p.name,p.kundennr,m.name,m.qr,b.qty,m.unit,locName(b.loc),isOffice()?m.price||'':'',isOffice()&&m.price?Math.round(b.qty*m.price*100)/100:'',person(b.by).name]);
  })});
  mrows.sort(function(a,b){return b[0]-a[0]});
  sheet('Materialbuchungen',['Datum','Projekt','Kundennr.','Material','QR','Menge','Einheit','Entnommen aus','Einkaufspreis €','Wert €','Gebucht von'],mrows,[14,28,11,34,10,9,9,14,14,10,18]);
  sheet('Lager',['QR','Material','Einheit','Bestand gesamt'].concat(LOCS.map(function(l){return l.n}),['Mindestbestand','Unter Mindestbestand','Einkaufspreis €','Lagerwert €','Lieferant','Artikelnr.','Notiz']),
    S.mats.slice().sort(function(a,b){return a.name.localeCompare(b.name,'de')}).map(function(m){
      return [m.qr,m.name,m.unit,m.stock].concat(LOCK.map(function(k){return m.locs[k]}),[m.min,isLow(m)?'Ja':'Nein',m.price||'',m.price?Math.round(m.stock*m.price*100)/100:'',m.supplier,m.artnr,m.note]);
    }),[10,36,9,12,12,9,11,11,14,12,14,12,22,16,30]);
  var drows=[];
  S.mats.forEach(function(m){m.deliveries.forEach(function(d){drows.push([dt(d.at),m.name,m.qr,d.qty,m.unit,locName(d.loc),d.supplier,d.note,person(d.by).name])})});
  drows.sort(function(a,b){return b[0]-a[0]});
  sheet('Lieferungen',['Datum','Material','QR','Menge','Einheit','Lagerort','Lieferant','Notiz / Lieferschein','Erfasst von'],drows,[14,36,10,9,9,13,22,26,18]);
  var trows=[];
  S.mats.forEach(function(m){transferPairs(m).forEach(function(t){trows.push([dt(t.at),m.name,m.qr,t.qty,m.unit,locName(t.from),locName(t.to),person(t.by).name])})});
  trows.sort(function(a,b){return b[0]-a[0]});
  sheet('Umbuchungen',['Datum','Material','QR','Menge','Einheit','Von','Nach','Gebucht von'],trows,[14,36,10,9,9,13,13,18]);
  sheet('Aufgaben',['Aufgabe','Projekt','Kundennr.','Bearbeiter','Termin','Uhrzeit','Status','Erledigt am','Angelegt am','Angelegt von'],
    S.tasks.slice().sort(function(a,b){return b.created-a.created}).map(function(t){
      return [t.name,pn(t.project),pk(t.project),t.assignee?person(t.assignee).name:'',t.due?new Date(t.due+'T12:00'):'',String(t.time||'').slice(0,5),t.done?'Erledigt':'Offen',dt(t.doneAt),dt(t.created),t.by?person(t.by).name:''];
    }),[36,28,11,18,12,8,10,14,14,18]);
  var wbout=XLSX.write(wb,{bookType:'xlsx',type:'array',cellDates:true});
  var blob=new Blob([wbout],{type:'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet'});
  saveFile(blob,'strom-macher_Export_'+TODAY()+'.xlsx','application/vnd.openxmlformats-officedocument.spreadsheetml.sheet');
  toast('Excel-Datei erstellt');
}


/* ---------- Einstellungen, Team ---------- */
function ago(ms){
  if(!ms)return 'noch nie';
  var s=Math.round((Date.now()-ms)/1000);
  if(s<60)return 'gerade eben';if(s<3600)return 'vor '+Math.round(s/60)+' Min.';
  return new Date(ms).toLocaleString('de-AT',{day:'numeric',month:'numeric',hour:'2-digit',minute:'2-digit'});
}
function sheetUser(){
  var off=isOffice(),n=OB.length;
  var install=(!standalone&&isIOS)?'<p class="hint">Tipp: In Safari auf „Teilen“ tippen und „Zum Home-Bildschirm“ wählen. Dann startet die App wie eine normale App und funktioniert auch ohne Empfang.</p>':'';
  var body='<div class="form" style="gap:16px">'+
    '<div><div class="sec" style="margin-bottom:6px">Abgleich</div><p class="hint" style="font-size:14px;color:var(--ink)">'+(navigator.onLine?'Verbunden':'Kein Empfang')+' · zuletzt abgeglichen '+esc(ago(sync_.last||C.pulledAt))+'<br>'+(n?n+' Einträge warten auf die Übertragung.':'Alles übertragen.')+'</p>'+
    '<button class="btn wide" data-act="syncNow" style="margin-top:8px">Jetzt abgleichen</button></div>'+
    (off?'<div><div class="sec" style="margin-bottom:8px">Büro</div><div class="form" style="gap:10px"><button class="btn main wide" data-act="exportMenu">Export &amp; Ausdrucke</button><button class="btn wide" data-act="team">Team verwalten</button></div><p class="hint" style="margin-top:6px">Der Export enthält Projekte, Stunden, Materialbuchungen, Lager, Lieferungen und Aufgaben.</p></div>':'')+
    install+
    '<div><button class="btn '+(ui.confirm==='logout'?'danger':'')+' wide" data-act="logout">'+(ui.confirm==='logout'?(n?'Es warten noch '+n+' Einträge – trotzdem abmelden?':'Wirklich abmelden?'):'Abmelden')+'</button><p class="hint" style="margin-top:8px">Angemeldet als '+esc(ME.name)+' · '+(off?'Büro und Lager':'Monteur')+' · Version '+esc(CFG.version||'1')+'</p></div></div>';
  openSheet('user',sheetShell(ME.name,'Einstellungen',body,'92%'));
  if(off)loadScript('vendor/xlsx.full.min.js').catch(function(){});
}
function sheetTeam(){
  var rows=C.profiles.slice().sort(function(a,b){return a.name.localeCompare(b.name,'de')}).map(function(p){
    var self=p.id===ME.id,act=p.active!==false;
    return '<div class="trow"><input class="tin" value="'+esc(p.name)+'" data-change="pname" data-id="'+p.id+'" aria-label="Name" autocomplete="off"><div class="seg" style="min-width:150px"><button data-act="setRole" data-id="'+p.id+'" data-v="buero" class="'+(p.role==='buero'?'on':'')+'"'+(self?' disabled':'')+'>Büro</button><button data-act="setRole" data-id="'+p.id+'" data-v="monteur" class="'+(p.role==='monteur'?'on':'')+'"'+(self?' disabled':'')+'>Monteur</button></div>'+
      '<button class="btn small" data-act="setActive" data-id="'+p.id+'" data-v="'+(act?'0':'1')+'"'+(self?' disabled':'')+'>'+(act?'Sperren':'Freigeben')+'</button></div>';
  }).join('');
  var body='<div class="form" style="gap:14px"><div>'+rows+'</div><p class="hint">Neue Mitarbeiter lädst du im Supabase-Dashboard unter „Authentication → Users“ per „Invite user“ ein. Nach der ersten Anmeldung erscheinen sie hier und du legst die Rolle fest. Gesperrte Personen sehen keine Daten mehr.</p></div>';
  openSheet('team',sheetShell('Team','Zugänge und Rollen',body,'92%'));
}

/* ---------- Aktionen ---------- */
function setTab(t){
  if(ui.detail||ui.lead){ui.detail=null;ui.lead=null;renderDetail()}
  if(ui.sheetKind)closeSheet();
  ui.tab=t;renderHeader();var first=!ui.seen[t];ui.seen[t]=true;renderTab(first);
}
function checkTask(id,btn){
  var row=btn.closest('.task');
  if(ui.pend[id]){clearTimeout(ui.pend[id].a);clearTimeout(ui.pend[id].b);delete ui.pend[id];row.classList.remove('is-done','leaving');return}
  row.classList.add('is-done');
  ui.pend[id]={a:setTimeout(function(){
    row.classList.add('leaving');
    ui.pend[id].b=setTimeout(function(){
      delete ui.pend[id];
      var t=S.tasks.filter(function(x){return x.id===id})[0];
      if(t)mut('tasks','up',{id:id,done:true,done_at:new Date().toISOString()});
    },210);
  },1500)};
}
function keepRender(fn){var L=$('#layer'),s=$('.sheet'),st=s?s.scrollTop:0;ui.keepFx=true;L.classList.add('nofx');fn();ui.keepFx=false;var n=$('.sheet');if(n)n.scrollTop=st}
function sheetTasksAllKeep(){keepRender(sheetTasksAll)}

var actions={
  tab:function(el){setTab(el.dataset.tab)},
  home:function(){setTab('start')},
  user:function(){ui.confirm=null;sheetUser()},
  closeSheet:closeSheet,
  addTask:function(el){sheetTaskNew(el.dataset.pid||null)},
  allTasks:function(){ui.tm='active';sheetTasksAll()},
  tm:function(el){ui.tm=el.dataset.v;sheetTasksAllKeep()},
  tf:function(el){ui.tf=el.dataset.v;sheetTasksAllKeep()},
  chk:function(el){checkTask(el.dataset.id,el)},
  restoreTask:function(el){var t=S.tasks.filter(function(x){return x.id===el.dataset.id})[0];if(t){mut('tasks','up',{id:t.id,done:false,done_at:null});sheetTasksAllKeep();toast('Aufgabe wieder aktiv')}},
  setDate:function(el){var v=el.dataset.v;$('#td').value=v===''?'':dayOff(Number(v))},
  openProj:function(el){
    var wasSheet=ui.sheetKind;if(wasSheet)closeSheet();
    ui.lead=null;ui.detail=el.dataset.id;renderDetail();
  },
  closeDetail:function(){closeDetailAnimated()},
  newProj:function(){sheetProjForm(null)},
  editProj:function(){var p=proj(ui.detail);if(p)sheetProjForm(p)},
  projArchive:function(){sheetProjList('archive')},
  projSearch:function(){sheetProjList('search')},
  closeProj:function(el){
    if(ui.confirm!=='cp'){ui.confirm='cp';el.textContent='Wirklich abschließen?';clearTimeout(actions.closeProj.k);actions.closeProj.k=setTimeout(function(){ui.confirm=null;if(el.isConnected)el.textContent='Projekt abschließen'},3200);return}
    var p=proj(el.dataset.id);ui.confirm=null;mut('projects','up',{id:p.id,status:'archiv'});toast('„'+p.name+'“ ins Archiv verschoben');
  },
  reopenProj:function(){var p=proj(ui.detail);mut('projects','up',{id:p.id,status:'aktiv'});toast('Projekt wieder geöffnet')},
  newMat:sheetMatNew,
  matSearch:sheetMatList,
  openMat:function(el){sheetMatDetail(el.dataset.id)},
  delivery:function(el){openMatFlow('deliver',null,el.dataset.id)},
  book:function(el){openMatFlow('book',el.dataset.pid)},
  pickMat:function(el){ui.m.sel=el.dataset.id;ui.m.qty=1;ui.m.loc=null;sheetMat()},
  unpick:function(){ui.m.sel=null;ui.m.loc=null;sheetMat()},
  locList:function(el){sheetLocList(el.dataset.v)},
  transfer:function(el){sheetTransfer(el.dataset.id)},
  locPick:function(el){
    var g=el.dataset.g;if(!ui.m)return;ui.m[g]=el.dataset.v;
    el.parentNode.querySelectorAll('button').forEach(function(b){var on=b===el;b.classList.toggle('on',on);b.setAttribute('aria-pressed',String(on))});
    setErr(g,'');setErr('qty','');
  },
  qtyAll:function(){var mt=mat(ui.m.sel);if(mt)$('#qty').value=nf(mt.locs[ui.m.loc]||0,3).replace(/\./g,'')},
  delTr:function(el){
    var ids=el.dataset.ids.split(','),k='tr'+ids[0];
    if(ui.confirm!==k){ui.confirm=k;el.classList.add('arm');toast('Nochmal tippen, um die Umbuchung zu stornieren');setTimeout(function(){if(ui.confirm===k)ui.confirm=null;if(el.isConnected)el.classList.remove('arm')},3000);return}
    ui.confirm=null;ids.forEach(function(id){mut('stock_moves','del',{id:id})});toast('Umbuchung storniert');keepRender(function(){sheetMatDetail(el.dataset.id)});
  },
  qtyAdd:function(el){var i=$('#qty');i.value=nf(num('qty')+Number(el.dataset.v),3).replace(/\./g,'')},
  qtyStep:function(el){var i=$('#qty'),n=num('qty')||0;n=Math.max(0,n+Number(el.dataset.v));i.value=nf(n,3).replace(/\./g,'')},
  scan:function(el){sheetScan(el.dataset.next)},
  qr:function(el){sheetQR(el.dataset.id)},
  saveQr:function(el){saveQr(el.dataset.id)},
  hours:function(el){sheetHours(el.dataset.pid)},
  hAdd:function(el){ui.h.val=Math.max(0,ui.h.val+Number(el.dataset.v));hUpd()},
  hReset:function(){ui.h.val=0;hUpd()},
  delBk:function(el){
    var id=el.dataset.id;
    if(el.dataset.t==='h'){mut('hours','del',{id:id});toast('Stundenbuchung storniert')}
    else{mut('stock_moves','del',{id:id});toast('Storno: Bestand angepasst')}
  },
  photoCam:function(){$('#phCam').click()},
  photoGal:function(){$('#phGal').click()},
  viewPhoto:function(el){ui.confirm=null;sheetPhoto(el.dataset.id)},
  delPhoto:function(el){
    var id=el.dataset.id;
    if(ui.confirm!=='dp'+id){ui.confirm='dp'+id;keepRender(function(){sheetPhoto(id)});return}
    var p=proj(ui.detail),f=p.photos.filter(function(x){return x.id===id})[0];ui.confirm=null;
    closeSheet();mut('photos','delphoto',{id:id,path:f.path});toast('Foto gelöscht');
  },
  syncNow:function(){toast(navigator.onLine?'Abgleich läuft…':'Kein Empfang – es wird übertragen, sobald du wieder online bist');sync()},
  export:function(){exportXlsx()},
  exportAufmass:function(){exportProjekt(ui.detail)},
  exportMenu:function(){sheetExport()},
  shareFile:function(){var f=ui.shareFile;if(!f)return;navigator.share({files:[f]}).then(function(){closeSheet()}).catch(function(){})},
  expLoc:function(el){ui.exp.loc=el.dataset.v;document.querySelectorAll('#expLocs .chip').forEach(function(b){b.classList.toggle('on',b===el)})},
  expZero:function(el){ui.exp.zero=!ui.exp.zero;el.classList.toggle('on',ui.exp.zero);el.textContent=(ui.exp.zero?'✓ ':'')+'Auch Material ohne Bestand'},
  expLager:function(){exportLager(ui.exp.loc,ui.exp.zero)},
  expProj:function(el){exportProjekt(el.dataset.id)},
  team:sheetTeam,
  setRole:function(el){var p=C.profiles.filter(function(x){return x.id===el.dataset.id})[0];if(p&&p.role!==el.dataset.v){mut('profiles','up',{id:p.id,role:el.dataset.v});keepRender(sheetTeam)}},
  setActive:function(el){var p=C.profiles.filter(function(x){return x.id===el.dataset.id})[0];if(p){mut('profiles','up',{id:p.id,active:el.dataset.v==='1'});keepRender(sheetTeam)}},
  logout:async function(){
    if(ui.confirm!=='logout'){ui.confirm='logout';keepRender(sheetUser);return}
    try{await sb.auth.signOut()}catch(e){}
    await idb.clear();try{localStorage.clear()}catch(e){}
    location.replace(location.pathname);
  },
  authSwitch:function(el){showAuth(el.dataset.v)},
  authReload:function(){location.reload()}
};
var submits={
  saveTask:submitTask,saveProj:submitProj,saveMat:submitMatNew,
  saveMatEdit:function(f){submitMatEdit(f.dataset.id)},
  saveBook:submitBook,saveDelivery:submitDelivery,saveTransfer:submitTransfer,saveHours:submitHours,scanManual:submitScanManual,
  login:doLogin,reset:doReset,setpw:doSetPw
};

/* Schnelles Doppeltippen auf Buttons soll nicht zoomen (Fallback, falls touch-action nicht greift) */
(function(){
  var last=0,moved=false;
  document.addEventListener('touchstart',function(){moved=false},{passive:true});
  document.addEventListener('touchmove',function(){moved=true},{passive:true});
  document.addEventListener('touchend',function(e){
    var now=Date.now(),b=e.target.closest&&e.target.closest('button,[data-act],.chip');
    if(b&&!moved&&now-last<450&&!b.disabled){e.preventDefault();b.click()}
    last=now;
  },{passive:false});
})();
document.addEventListener('click',function(e){
  var el=e.target.closest('[data-act]');if(!el||el.disabled)return;
  var fn=actions[el.dataset.act];if(fn){fn(el)}
});
document.addEventListener('submit',function(e){
  var f=e.target.closest('form[data-submit]');if(!f)return;
  e.preventDefault();var fn=submits[f.dataset.submit];if(fn)fn(f);
});
document.addEventListener('input',function(e){
  var q=e.target.closest('[data-filter]');if(!q)return;
  var v=q.value.trim().toLowerCase(),kind=q.dataset.filter;
  if(kind==='proj'){
    var r=projRows(v,false);$('#flist').innerHTML=r.html;var nr=$('#nores');if(nr)nr.hidden=r.total>0;return;
  }
  if(kind==='expproj'){$('#elist').innerHTML=expProjRows(v);return}
  if(kind==='tp'){var s=$('#tp');if(s)s.innerHTML=projOptions(v,s.value,60);return}
  var n=0;
  var words=v.split(/\s+/).filter(Boolean);
  document.querySelectorAll('#flist .item').forEach(function(it){var dq=it.dataset.q;var hit=words.every(function(w){return dq.indexOf(w)>-1});it.hidden=!hit;if(hit)n++});
  var nr2=$('#nores');if(nr2)nr2.hidden=n>0;
});
document.addEventListener('change',function(e){
  var c=e.target.closest('[data-change]');if(!c)return;
  if(vchange[c.dataset.change]){vchange[c.dataset.change](c);return}
  if(c.dataset.change==='pname'){var nm=c.value.trim();if(nm)mut('profiles','up',{id:c.dataset.id,name:nm});else toast('Ein Name darf nicht leer sein.')}
});
document.addEventListener('keydown',function(e){if(e.key==='Escape'&&ui.sheetKind)closeSheet()});
['phCam','phGal'].forEach(function(id){
  var i=document.createElement('input');i.type='file';i.accept='image/*';i.id=id;i.hidden=true;if(id==='phGal')i.multiple=true;else i.setAttribute('capture','environment');
  i.addEventListener('change',onPhoto);document.getElementById('app').appendChild(i);
});

/* ---------- Anmeldung ---------- */
ui.view='boot';
function authShell(inner){
  return '<div class="authbox"><svg class="alg" viewBox="0 0 3067 3610" aria-hidden="true"><use href="#sm-logo"/></svg><h1>strom-macher</h1>'+inner+'</div>';
}
function showAuth(kind,msg){
  ui.view='auth';stopScan();
  var L=$('#layer');L.innerHTML='';ui.sheetKind='';
  var a=$('#auth');a.hidden=false;
  var note=msg?'<p class="amsg">'+esc(msg)+'</p>':'';
  var h='';
  if(kind==='boot'){h=authShell('<p class="hint" style="text-align:center">Wird geladen…</p>')}
  else if(kind==='login'){
    h=authShell('<form class="form" data-submit="login" novalidate>'+
      fld('le','E-Mail','<input id="le" type="email" autocomplete="username" inputmode="email" autocapitalize="off">')+
      fld('lp','Passwort','<input id="lp" type="password" autocomplete="current-password">')+note+
      '<button class="btn main wide" type="submit" id="lb">Anmelden</button>'+
      '<button class="alink" type="button" data-act="authSwitch" data-v="reset">Passwort vergessen?</button></form>');
  }else if(kind==='reset'){
    h=authShell('<form class="form" data-submit="reset" novalidate><p class="hint">Wir schicken dir einen Link zum Festlegen eines neuen Passworts.</p>'+
      fld('le','E-Mail','<input id="le" type="email" autocomplete="username" inputmode="email" autocapitalize="off">')+note+
      '<button class="btn main wide" type="submit" id="lb">Link senden</button>'+
      '<button class="alink" type="button" data-act="authSwitch" data-v="login">Zurück zur Anmeldung</button></form>');
  }else if(kind==='setpw'){
    h=authShell('<form class="form" data-submit="setpw" novalidate><p class="hint" style="text-align:center">Lege dein Passwort fest (mindestens 8 Zeichen).</p>'+
      fld('np','Neues Passwort','<input id="np" type="password" autocomplete="new-password">')+
      fld('np2','Wiederholen','<input id="np2" type="password" autocomplete="new-password">')+note+
      '<button class="btn main wide" type="submit" id="lb">Passwort speichern</button></form>');
  }else if(kind==='wait'){
    h=authShell('<div class="form"><p class="amsg" style="text-align:center">Dein Zugang ist angelegt, aber noch nicht freigeschaltet. Bitte melde dich im Büro.</p><button class="btn wide" data-act="authReload">Erneut prüfen</button><button class="btn wide" data-act="logout">Abmelden</button></div>');
  }
  a.innerHTML=h;
  var f=$('#le')||$('#np');if(f&&matchMedia('(hover:hover)').matches)f.focus();
  if(kind==='login'){try{var em=localStorage.getItem('sm-email');if(em&&$('#le')){$('#le').value=em;if($('#lp')&&matchMedia('(hover:hover)').matches)$('#lp').focus()}}catch(e){}}
}
function authErr(m){
  if(/invalid login/i.test(m))return 'E-Mail oder Passwort stimmt nicht.';
  if(/email not confirmed/i.test(m))return 'Die E-Mail-Adresse ist noch nicht bestätigt.';
  if(/rate limit|too many/i.test(m))return 'Zu viele Versuche. Bitte in ein paar Minuten erneut probieren.';
  if(/fetch|network|failed/i.test(m))return 'Keine Verbindung. Zum ersten Anmelden brauchst du Empfang.';
  if(/same password|different from the old/i.test(m))return 'Bitte ein anderes Passwort als bisher wählen.';
  if(/weak|at least/i.test(m))return 'Das Passwort ist zu schwach (mindestens 8 Zeichen).';
  return m;
}
async function doLogin(){
  var em=val('le'),pw=($('#lp')||{}).value||'';
  if(!em){setErr('le','Bitte die E-Mail-Adresse eingeben.');return}setErr('le','');
  if(!pw){setErr('lp','Bitte das Passwort eingeben.');return}setErr('lp','');
  var b=$('#lb');b.disabled=true;b.textContent='Anmelden…';
  var r=await sb.auth.signInWithPassword({email:em,password:pw});
  if(r.error){showAuth('login',authErr(r.error.message));$('#le').value=em;return}
  try{localStorage.setItem('sm-email',em)}catch(e){}
  SESSION=r.data.session;
  await afterLogin();
}
async function doReset(){
  var em=val('le');if(!em){setErr('le','Bitte die E-Mail-Adresse eingeben.');return}setErr('le','');
  var b=$('#lb');b.disabled=true;
  var r=await sb.auth.resetPasswordForEmail(em,{redirectTo:location.origin+location.pathname});
  showAuth('login',r.error?authErr(r.error.message):'Falls die Adresse bekannt ist, ist ein Link unterwegs.');
}
async function doSetPw(){
  var a=($('#np')||{}).value||'',b2=($('#np2')||{}).value||'';
  if(a.length<8){setErr('np','Mindestens 8 Zeichen.');return}setErr('np','');
  if(a!==b2){setErr('np2','Die Passwörter stimmen nicht überein.');return}setErr('np2','');
  var r=await sb.auth.updateUser({password:a});
  if(r.error){showAuth('setpw',authErr(r.error.message));return}
  history.replaceState(null,'',location.pathname);
  var s=await sb.auth.getSession();SESSION=s.data&&s.data.session;
  await afterLogin();
}
async function afterLogin(){
  if(C.me&&SESSION&&C.me.id!==SESSION.user.id){C=emptyC();OB=[];await idb.clear();build()}
  showAuth('boot');
  await sync();
  route();
}
function route(){
  if(!SESSION){showAuth('login');return}
  if(!C.me){showAuth('login',navigator.onLine?'Die Daten konnten nicht geladen werden. Bitte erneut versuchen.':'Keine Verbindung. Zum ersten Anmelden brauchst du Empfang.');return}
  if(C.me.missing||C.me.active===false){showAuth('wait');return}
  showApp();
}
function showApp(){
  ui.view='app';$('#auth').hidden=true;build();
  if(!ui.started){ui.started=true;ui.tab='start';ui.seen={start:true};var hm=String(location.hash||'').match(/lead=([^&]+)/);if(hm){ui.pendingLead=decodeURIComponent(hm[1]);try{history.replaceState(null,'',location.pathname+location.search)}catch(e){}}}
  renderHeader();renderTab(true);renderBubbles();
  if(!tryPendingLead())remind();
}
function remind(){
  try{
    var key='sm-remind',today=TODAY();if(localStorage.getItem(key)===today)return;
    var n=S.tasks.filter(function(t){return !t.done&&t.assignee===ME.id&&t.due&&t.due<=today}).length;
    if(!n)return;localStorage.setItem(key,today);
    var el=$('#push');
    el.innerHTML='<span class="pi">'+ico.bolt+'</span><div><b>strom-macher · Erinnerung</b><span>'+(n===1?'Eine Aufgabe ist':n+' Aufgaben sind')+' für dich heute fällig oder überfällig.</span></div>';
    el.classList.add('on');clearTimeout(remind.k);remind.k=setTimeout(function(){el.classList.remove('on')},6000);
  }catch(e){}
}

/* ---------- Vertrieb: PV-Leads mit Karte (übernommen aus der PV-Lead-Karte) ---------- */
var VST={eingang:'Eingang',spam:'Spam',offen:'Rückruf offen',nicht_erreicht:'Nicht erreicht',einplanen:'Eingeplant',wiedervorlage:'Wiedervorlage',angeboten:'Angeboten',verworfen:'Verworfen',beauftragt:'Beauftragt',verloren:'Verloren'};
var VORDER=['offen','nicht_erreicht','einplanen','angeboten','wiedervorlage','verworfen','beauftragt','verloren'];
var VDATED=['einplanen','wiedervorlage'];
var VGONE=['verworfen','beauftragt','verloren'];
var VBTN=[['nicht_erreicht','Nicht erreicht'],['einplanen','Einplanen'],['wiedervorlage','Wiedervorlage'],['angeboten','Angeboten'],['beauftragt','Beauftragt'],['verloren','Verloren'],['verworfen','Verwerfen']];
var VSRC=[['Tuny','tunyCRM'],['SM','solarmaker'],['Empf','Empfehlung'],['Web','Website']];
var VSP=[['pv','Photovoltaik'],['verteiler','Verteiler'],['elektro','Hauselektrik'],['stoerung','Störung'],['sonstiges','Sonstiges']];
var SPC={verteiler:'#0B5E8E',elektro:'#B98600',stoerung:'#B98600',sonstiges:'#59636F'};
var SPT={verteiler:'V',elektro:'E',stoerung:'!',sonstiges:'?'};
function spLabel(k){for(var i=0;i<VSP.length;i++)if(VSP[i][0]===k)return VSP[i][1];return 'Photovoltaik'}
function isPv(l){return !l.sp||l.sp==='pv'}
function flagTxt(l){return isPv(l)?fmtK(l.k):SPT[l.sp]||'?'}
var HQ={lat:48.087,lon:16.302,label:'Grenzgasse 40, 2340 Mödling'};
var V_ARCH=28*864e5;
var vui={sp:'',prism:true,arch:false,zoom:null,sig:'',edit:null,geo:null,busy:false};

function buildLeads(){
  var logs={};
  (C.lead_log||[]).forEach(function(e){(logs[e.lead_id]=logs[e.lead_id]||[]).push({id:e.id,text:e.text,at:msOf(e.at),by:e.created_by,byName:e.by_name||''})});
  S.leads=(C.leads||[]).map(function(r){
    var kEst=r.kwp_est==null||r.kwp_est===''?null:Number(r.kwp_est),kOv=r.kwp==null||r.kwp===''?null:Number(r.kwp);
    var k=kOv!=null?kOv:kEst;
    var n=function(x){return x==null||x===''||!isFinite(Number(x))?null:Number(x)};
    return {id:r.id,name:r.name||'Unbekannt',short:r.short||shortOf(r.name||'Lead'),anrede:r.anrede||'',phone:r.phone||'',phone2:r.phone2||'',email:r.email||'',
      addr:r.addr||'',ort:r.ort||'',objekt:r.objekt||'',ausrichtung:r.ausrichtung||'',dach:r.dach||'',verbrauch:r.verbrauch||'',speicher:r.speicher||'',
      wuensche:r.wuensche||'',budget:r.budget||'',umsetzung:r.umsetzung||'',personen:r.personen||'',eingang:r.eingang||'',info:r.info||'',last:r.last_info||'',
      kb:r.kwp_basis||'',kEst:kEst,kOv:kOv,k:k,src:r.source||'Tuny',lat:n(r.lat),lon:n(r.lon),km:n(r.km),min:n(r.min),
      st:r.status||'offen',stAt:msOf(r.status_at),termin:r.termin||'',inviteAt:msOf(r.invite_at),inviteT:r.invite_termin||'',
      sp:r.sparte||'pv',notiz:r.notiz||'',notizAt:msOf(r.notiz_at),hist:Array.isArray(r.src_hist)?r.src_hist:[],created:msOf(r.created_at),
      log:(logs[r.id]||[]).sort(function(a,b){return b.at-a.at})};
  });
}
var lead=function(id){return (S.leads||[]).filter(function(l){return l.id===id})[0]};
var isArchLead=function(l){return l.st==='verworfen'&&l.stAt&&(Date.now()-l.stAt)>V_ARCH};
function srcLabel(s){for(var i=0;i<VSRC.length;i++)if(VSRC[i][0]===s)return VSRC[i][1];return s||'–'}
function fmtK(k){return k==null?'?':(Math.round(k*10)/10).toString().replace('.',',')}
function fmtKm(l){if(l.km==null)return 'Entfernung unbekannt';return (l.km<10?l.km.toFixed(1).replace('.',','):Math.round(l.km))+' km · '+fmtMin(l.min||0)}
function fmtMin(m){m=Math.round(m);return m<60?m+' min':Math.floor(m/60)+' h '+String(m%60).padStart(2,'0')}
function fmtTermin(v){
  if(!v)return '';var x=new Date(v);if(isNaN(x))return '';
  return x.toLocaleDateString('de-AT',{weekday:'short',day:'2-digit',month:'2-digit',year:'numeric'})+', '+x.toLocaleTimeString('de-AT',{hour:'2-digit',minute:'2-digit'})+' Uhr';
}
function fmtStamp(ms){return ms?new Date(ms).toLocaleString('de-AT',{dateStyle:'short',timeStyle:'short'}):''}
function vMax(){var m=0;(S.leads||[]).forEach(function(l){if(isPv(l)&&l.k!=null&&l.k>m)m=l.k});return m||1}
function hsl2hex(h,s,l){
  h=((h%360)+360)%360;var c=(1-Math.abs(2*l-1))*s,x=c*(1-Math.abs((h/60)%2-1)),m=l-c/2,r=0,g=0,b=0;
  if(h<60){r=c;g=x}else if(h<120){r=x;g=c}else if(h<180){g=c;b=x}else if(h<240){g=x;b=c}else if(h<300){r=x;b=c}else{r=c;b=x}
  var hx=function(v){return ('0'+Math.round((v+m)*255).toString(16)).slice(-2)};return '#'+hx(r)+hx(g)+hx(b);
}
function prism(k,max){return hsl2hex(270-270*Math.min(1,k/max),0.75,0.5)}
function leadColor(l,max){if(!isPv(l))return SPC[l.sp]||'#59636F';return l.k==null?'#888780':(vui.prism?prism(l.k,max||vMax()):'#2F7FD0')}
function kmFrom(lat,lon){
  var R=6371,rad=Math.PI/180,dl=(lat-HQ.lat)*rad,dn=(lon-HQ.lon)*rad;
  var a=Math.sin(dl/2)*Math.sin(dl/2)+Math.cos(HQ.lat*rad)*Math.cos(lat*rad)*Math.sin(dn/2)*Math.sin(dn/2);
  var air=2*R*Math.asin(Math.sqrt(a)),road=air*1.3;
  return {km:Math.round(road*10)/10,min:Math.round(road*0.65+6)};
}
var XSVG='<svg class="lx" viewBox="0 0 64 48" preserveAspectRatio="none" aria-hidden="true"><g stroke-linecap="round"><line x1="6" y1="6" x2="58" y2="42" stroke="#fff" stroke-width="7"/><line x1="58" y1="6" x2="6" y2="42" stroke="#fff" stroke-width="7"/><line x1="6" y1="6" x2="58" y2="42" stroke="#E5483A" stroke-width="4"/><line x1="58" y1="6" x2="6" y2="42" stroke="#E5483A" stroke-width="4"/></g></svg>';

function RM(){return !!(window.matchMedia&&matchMedia('(prefers-reduced-motion: reduce)').matches)}
/* Startauswahl */
function tabStart(){
  var hr=new Date().getHours(),g=hr<11?'Guten Morgen':hr<18?'Guten Tag':'Guten Abend';
  var L=S.leads||[],now=new Date(),wk=new Date(now.getTime()+7*864e5);
  var open=L.filter(function(l){return l.st==='offen'||l.st==='nicht_erreicht'}).length,inb=L.filter(function(l){return l.st==='eingang'}).length;
  var soon=L.filter(function(l){if(!VDATED.includes(l.st)||!l.termin)return false;var t=new Date(l.termin);return t>=new Date(now.getTime()-36e5)&&t<=wk}).length;
  var tasks=S.tasks.filter(function(t){return !t.done}).length,heute=activeProjects().filter(function(p){return p.termin===TODAY()}).length;
  return '<div class="home start"><svg class="lg rise" style="--i:0" viewBox="0 0 3067 3610" role="img" aria-label="strom-macher Logo"><use href="#sm-logo"/></svg>'+
    '<h1 class="rise" style="--i:1">strom-macher</h1><p class="hi rise" style="--i:1">'+g+', '+esc(first(ME.name))+'</p>'+
    '<div class="hbtns">'+
    '<button class="hbtn vbtn rise" style="--i:2" data-act="tab" data-tab="vertrieb"><span>Vertrieb<em>Leads · Karte · Termine</em></span><small>'+(inb?'<b class="newb">'+inb+(inb===1?' neue Anfrage':' neue Anfragen')+'</b><br>':'')+open+(open===1?' Rückruf offen':' Rückrufe offen')+'<br>'+soon+(soon===1?' Termin':' Termine')+' in 7 Tagen</small></button>'+
    '<button class="hbtn bbtn rise" style="--i:3" data-act="tab" data-tab="aufgaben"><span><i class="sq3" aria-hidden="true"><b></b><b></b><b></b></i>Betrieb<em>Aufgaben · Lager · Projekte</em></span><small>'+tasks+' Aufgaben offen<br>'+heute+(heute===1?' Termin heute':' Termine heute')+'</small></button>'+
    '</div></div>';
}

/* Vertrieb: Übersicht */
function leadCard(l,max){
  var s=l.st,dated=VDATED.includes(s);
  var note=l.notiz?'<span class="lc-n">✎ '+esc(l.notiz.split('\n')[0].slice(0,60))+(l.notiz.length>60?'…':'')+'</span>':'';
  var term=dated?'<span class="lc-t">'+(s==='wiedervorlage'?'Wiedervorlage':'Termin')+': '+(l.termin?esc(fmtTermin(l.termin)):'noch offen')+'</span>':'';
  return '<button class="lcard s-'+s+'" data-act="openLead" data-id="'+esc(l.id)+'"><span class="lsw" style="background:'+leadColor(l,max)+'"><b class="num">'+esc(flagTxt(l))+'</b>'+XSVG+'</span>'+
    '<span class="grow"><span class="t">'+esc(l.short)+' <i class="src">'+esc(isPv(l)?l.src:spLabel(l.sp))+'</i></span><span class="s">'+esc(l.ort||city(l.addr))+' · '+esc(fmtKm(l))+'</span>'+term+note+'</span></button>';
}
function vSpOk(l){return !vui.sp||(vui.sp==='elektro'?(l.sp==='elektro'||l.sp==='stoerung'):l.sp===vui.sp)}
function tabVertrieb(){
  var L=S.leads||[],max=vMax();
  var inbox=L.filter(function(l){return l.st==='eingang'}).sort(function(a,b){return b.created-a.created});
  var nSpam=L.filter(function(l){return l.st==='spam'}).length;
  var arr=L.filter(function(l){return l.st!=='eingang'&&l.st!=='spam'&&(vui.arch||!isArchLead(l))&&vSpOk(l)});
  var nArch=L.filter(isArchLead).length;
  var tk=function(l){return VDATED.includes(l.st)?(l.termin||'9999'):''};
  arr.sort(function(a,b){return VORDER.indexOf(a.st)-VORDER.indexOf(b.st)||(tk(a)<tk(b)?-1:tk(a)>tk(b)?1:0)||((b.k==null?-1:b.k)-(a.k==null?-1:a.k))});
  var groups=VORDER.map(function(s){
    var it=arr.filter(function(l){return l.st===s});
    var head='<div class="sec g-'+s+'"><span>'+VST[s]+' <span class="num">('+it.length+')</span></span>'+(s==='verworfen'&&nArch?'<button class="btn small" data-act="vArch">'+(vui.arch?'Ältere ausblenden':nArch+' älter als 4 Wochen')+'</button>':'')+'</div>';
    return '<div class="vgrp">'+head+(it.length?'<div class="lcards">'+it.map(function(l){return leadCard(l,max)}).join('')+'</div>':'<p class="hint vempty">'+(s==='offen'?'Keine offenen Rückrufe.':'Keine Leads in diesem Status.')+'</p>')+'</div>';
  }).join('');
  var inboxHtml=inbox.length?'<div class="vinbox"><div class="sec"><span>Eingang · zum Zuordnen <span class="num">('+inbox.length+')</span></span></div>'+
    inbox.map(function(l){return '<div class="vin"><button class="vin-t" data-act="openLead" data-id="'+esc(l.id)+'"><b>'+esc(l.name)+'</b><span>'+esc(l.ort||'')+(l.eingang?' · '+esc(l.eingang):'')+'</span><span class="vin-m">'+esc((l.info||'').slice(0,110))+((l.info||'').length>110?'…':'')+'</span></button>'+
      '<div class="vin-a">'+[['pv','PV'],['verteiler','Verteiler'],['elektro','Elektro'],['spam','Spam']].map(function(x){return '<button class="chip'+(x[0]==='spam'?' ghost':'')+'" data-act="leadAssign" data-id="'+esc(l.id)+'" data-v="'+x[0]+'">'+x[1]+'</button>'}).join('')+'</div></div>'}).join('')+'</div>':'';
  var grad='linear-gradient(to right,'+[0,.1,.2,.3,.4,.5,.6,.7,.8,.9,1].map(function(f){return prism(f*max,max)}).join(',')+')';
  var spChips=[['','Alle'],['pv','PV'],['verteiler','Verteiler'],['elektro','Elektro']].map(function(x){return '<button class="chip'+(vui.sp===x[0]?' on':'')+'" data-act="vSp" data-v="'+x[0]+'" aria-pressed="'+(vui.sp===x[0])+'">'+x[1]+'</button>'}).join('');
  var moved=vui.zoom&&(Math.abs(vui.zoom.k-1)>.01||Math.abs(vui.zoom.x)>2||Math.abs(vui.zoom.y)>2);
  return '<div class="titlebar rise" style="--i:0"><div class="pill">Vertrieb</div><button class="plus" data-act="leadNew" aria-label="Neuer Lead">+</button></div>'+
    '<div class="body" id="vbody">'+inboxHtml+'<div id="vcap" class="vcap">'+
    '<div class="vtools noshot">'+spChips+'<span class="vsep"></span><button class="chip" data-act="vPrism">'+(vui.prism?'Prisma aus':'Prisma an')+'</button><button class="chip" data-act="vReset" id="vreset"'+(moved?'':' hidden')+'>Ansicht zurücksetzen</button><button class="chip" data-act="vSnap">Snapshot</button>'+(nSpam?'<button class="chip ghost" data-act="vSpam">Spam ('+nSpam+')</button>':'')+'</div>'+
    '<div class="vshot-h" hidden><b>PV-Lead-Karte</b> · Stand '+esc(fmtStamp(Date.now()))+'</div>'+
    '<div class="vmap" id="vmap" aria-label="Karte Niederösterreich und Wien mit Lead-Fähnchen"><p class="hint vml">Karte wird geladen…</p></div>'+
    '<div class="vleg"><span class="lg">0 kWp <i class="grad" style="background:'+grad+'"></i> '+esc(fmtK(max))+' kWp</span><span class="lg"><i class="sq" style="background:'+SPC.verteiler+'"></i>Verteiler</span><span class="lg"><i class="sq" style="background:'+SPC.elektro+'"></i>Elektro/Störung</span><span class="lg"><i class="sq" style="background:#888780"></i>kWp unbekannt</span>'+
    '<span class="lg"><i class="sq o" style="border-color:var(--yellow)"></i>nicht erreicht</span><span class="lg"><i class="sq o" style="border-color:var(--blue)"></i>eingeplant</span>'+
    '<span class="lg"><i class="ln" style="background:#E8A33D"></i>Autobahn</span><span class="lg"><i class="ln d"></i>Bahn</span><span class="lg"><i class="ln" style="background:#3B82C4"></i>Flüsse</span></div>'+
    groups+'</div></div>';
}
function vSig(){return JSON.stringify([vui.sp,vui.prism,vui.arch,(C.leads||[]).length,C.leads,(C.lead_log||[]).length])}

/* Karte (D3, alle Daten lokal – funktioniert offline) */
var vlibs=null;
function loadMapLibs(){
  if(!vlibs)vlibs=Promise.all([loadScript('vendor/d3.min.js'),loadScript('vendor/topojson-client.min.js'),loadScript('vendor/leadmap-geo.js')]).catch(function(e){vlibs=null;throw e});
  return vlibs;
}
function mountMap(){
  var el=$('#vmap');if(!el)return;
  loadMapLibs().then(function(){if($('#vmap')===el)drawMap(el)}).catch(function(){el.innerHTML='<p class="hint vml">Karte konnte nicht geladen werden. Beim ersten Öffnen braucht die App Empfang.</p>'});
}
function drawMap(el,opts){
  opts=opts||{};
  var sel=opts.sel?lead(opts.sel):null,detail=!!opts.sel;
  var GEO=window.SM_GEO,W=1000,cw=el.clientWidth||1000,ch=el.clientHeight||620,H=detail?Math.max(240,Math.round(W*ch/cw)):620,max=vMax();
  el.innerHTML='';
  var L=(S.leads||[]).filter(function(l){return l.lat!=null&&l.lon!=null});
  var onMap=L.filter(function(l){return (['offen','nicht_erreicht','einplanen'].indexOf(l.st)>-1&&(!vui.sp||vSpOk(l)))||(sel&&l.id===sel.id)});
  var svg=d3.select(el).append('svg').attr('viewBox','0 0 '+W+' '+H).attr('preserveAspectRatio','xMidYMid slice').attr('role','img').attr('aria-label','Karte mit '+onMap.length+' Leads');
  var pts=[[15.18,47.68],[16.62,48.24]].concat(L.map(function(l){return [l.lon,l.lat]}));
  var pj=detail?d3.geoMercator().fitExtent([[14,14],[W-14,H-14]],{type:'MultiPoint',coordinates:pts})
    :d3.geoMercator().fitExtent([[14,30],[W-14,H-14]],{type:'MultiPoint',coordinates:[[15.98,47.93],[16.55,48.29]]});
  /* Grenzen aller Leads in Kartenkoordinaten: so weit darf man herauszoomen und verschieben */
  var bx=pts.map(function(c){return pj(c)}),bx0=Math.min(0,d3.min(bx,function(p){return p[0]})-60),by0=Math.min(0,d3.min(bx,function(p){return p[1]})-60),
      bx1=Math.max(W,d3.max(bx,function(p){return p[0]})+60),by1=Math.max(H,d3.max(bx,function(p){return p[1]})+60),
      kMin=detail?1:Math.max(0.2,Math.min(1,W/(bx1-bx0),H/(by1-by0)));
  var path=d3.geoPath(pj),line=d3.line().x(function(p){return pj(p)[0]}).y(function(p){return pj(p)[1]});
  var root=svg.append('g'),gLand=root.append('g'),gNet=root.append('g'),gTown=root.append('g'),gF=root.append('g');
  var feats=topojson.feature(GEO.AT,GEO.AT.objects.aut).features;
  gLand.selectAll('path').data(feats).join('path').attr('d',path).attr('class',function(d){return d.properties.name==='Wien'?'lw':'ll'}).attr('vector-effect','non-scaling-stroke');
  gNet.selectAll('.rv').data(GEO.G.riv).join('path').attr('d',line).attr('class','rv');
  gNet.selectAll('.lk').data(GEO.G.lake).join('path').attr('d',line).attr('class','lk');
  gNet.selectAll('.rl').data(GEO.G.rail).join('path').attr('d',line).attr('class','rl');
  gNet.selectAll('.rd').data(GEO.G.roads).join('path').attr('d',function(d){return line(d[1])}).attr('class',function(d){return d[0]==='M'?'rd m':'rd'});
  gNet.selectAll('path').attr('vector-effect','non-scaling-stroke');
  var tw=gTown.selectAll('g').data(GEO.T).join('g').attr('transform',function(d){var p=pj([d[1],d[2]]);return 'translate('+p[0]+','+p[1]+')'});
  tw.append('circle').attr('r',function(d){return d[3]?4:2.6}).attr('class','tc');
  tw.append('text').attr('class',function(d){return 'town'+(d[3]?' big':'')}).attr('x',6).attr('y',13).text(function(d){return d[0]});
  var sp=pj([HQ.lon,HQ.lat]),sg=gTown.append('g').attr('transform','translate('+sp[0]+','+sp[1]+')');
  sg.append('rect').attr('x',-6).attr('y',-6).attr('width',12).attr('height',12).attr('class','hq');sg.append('text').attr('class','town big').attr('x',9).attr('y',-6).text('Start');
  var fl=gF.selectAll('g.flag').data(onMap.slice().sort(function(a,b){if(sel){if(a.id===sel.id)return 1;if(b.id===sel.id)return -1}return b.lat-a.lat})).join(function(en){
    var g=en.append('g').attr('class','flag').attr('tabindex',0).attr('role','button');
    g.append('rect').attr('class','fhit').attr('x',-10).attr('y',-44).attr('height',54).attr('rx',8);
    g.append('circle').attr('r',3).attr('class','fp');g.append('line').attr('y2',-32).attr('class','fs');
    g.append('rect').attr('x',1).attr('y',-32).attr('height',18).attr('rx',2).attr('class','fr');
    g.append('text').attr('class','kt').attr('x',6).attr('y',-19);return g});
  fl.classed('sel',function(d){return !!sel&&d.id===sel.id}).classed('dim',function(d){return !!sel&&d.id!==sel.id})
    .attr('aria-label',function(d){return d.name+', '+(isPv(d)?fmtK(d.k)+' kWp':spLabel(d.sp))})
    .on('click',function(e,d){if(!sel||d.id!==sel.id)openLead(d.id)}).on('keydown',function(e,d){if(e.key==='Enter'||e.key===' '){e.preventDefault();openLead(d.id)}});
  fl.select('text.kt').text(function(d){return flagTxt(d)});
  fl.select('.fr').attr('fill',function(d){return leadColor(d,max)}).attr('class',function(d){return 'fr s-'+d.st});
  fl.each(function(d){
    var g=d3.select(this),w=g.select('text.kt').node().getComputedTextLength()+11;d._w=w;g.select('rect.fr').attr('width',w);g.select('rect.fhit').attr('width',w+20);
    var right=pj([d.lon,d.lat])[0]>W-90,dx=right?-4:w+4,dt=g.append('text').attr('class','dist').attr('text-anchor',right?'end':'start');
    if(d.km!=null){dt.append('tspan').attr('x',dx).attr('y',-24).text((d.km<10?d.km.toFixed(1).replace('.',','):Math.round(d.km))+' km');dt.append('tspan').attr('x',dx).attr('y',-15).text(fmtMin(d.min||0))}
  });
  var k0=1;
  /* Fähnchen in Bildschirmgröße denken: am Handy wird die 1000er-Karte stark verkleinert, darum größer zeichnen.
     Beim Hineinzoomen wachsen sie sichtbar mit (Bildschirmgröße steigt mit k^0,65), aber langsamer als die Karte. */
  function fscale(){var w=el.clientWidth||1000;return Math.max(1,Math.min(2.6,(1000/w)*0.85))}
  function fs(k){return fscale()/Math.pow(Math.max(k,1),0.35)}
  function place(k){
    var s=fs(k),ts=Math.max(1,fscale()*0.8)/Math.pow(Math.max(k,1),0.6);
    fl.attr('transform',function(d){var p=pj([d.lon,d.lat]);return 'translate('+p[0]+','+p[1]+') scale('+(sel&&d.id===sel.id?s*1.3:s)+')'});
    tw.selectAll('text,circle').attr('transform','scale('+ts+')');sg.attr('transform','translate('+sp[0]+','+sp[1]+') scale('+ts+')');
  }
  /* Tipp knapp neben ein Fähnchen: nächstgelegenes öffnen (bis ca. 24 px am Bildschirm) */
  svg.on('click',function(e){
    if(e.defaultPrevented)return;
    if(e.target.closest&&e.target.closest('.flag'))return;
    var pt=d3.pointer(e,root.node()),r=svg.node().getBoundingClientRect(),pxPerUnit=Math.max(r.width/W,r.height/H)*k0,best=null,bd=1e9,s=fs(k0);
    onMap.forEach(function(d){if(sel&&d.id===sel.id)return;var p=pj([d.lon,d.lat]),x0=p[0]-10*s,x1=p[0]+((d._w||24)+10)*s,y0=p[1]-44*s,y1=p[1]+10*s;
      var dx=Math.max(x0-pt[0],0,pt[0]-x1)*pxPerUnit,dy=Math.max(y0-pt[1],0,pt[1]-y1)*pxPerUnit,dd=Math.sqrt(dx*dx+dy*dy);if(dd<bd){bd=dd;best=d}});
    if(best&&bd<=24)openLead(best.id);
  });
  /* Alle Finger an d3 geben (sonst fehlt beim Zwei-Finger-Zoom der erste Finger); iOS-Seitenzoom auf der Karte unterbinden */
  var zoom=d3.zoom().scaleExtent([kMin,14]).translateExtent(detail?[[-W*0.1,-H*0.1],[W*1.1,H*1.1]]:[[bx0,by0],[bx1,by1]])
    .on('zoom',function(e){k0=e.transform.k;root.attr('transform',e.transform);place(k0);
      if(!detail){var t=e.transform,moved=Math.abs(t.k-1)>.01||Math.abs(t.x)>2||Math.abs(t.y)>2;vui.zoom=moved?t:null;var rb=$('#vreset');if(rb)rb.hidden=!moved}});
  svg.call(zoom).on('dblclick.zoom',null);
  el.style.touchAction='none';
  ['gesturestart','gesturechange','gestureend'].forEach(function(ev){el.addEventListener(ev,function(x){x.preventDefault()},{passive:false})});
  function focusT(l){var p=pj([l.lon,l.lat]),k=Math.max(4,k0);return d3.zoomIdentity.translate(W/2-k*p[0],H*0.7-k*p[1]).scale(k)}
  if(detail){
    /* Lead im Streifen wechseln: Karte bleibt stehen und fährt zum neuen Fähnchen */
    el._go=function(id){
      var nl=lead(id);if(!nl)return false;
      if(!fl.filter(function(d){return d.id===id}).size())return false;
      sel=nl;
      fl.classed('sel',function(d){return d.id===id}).classed('dim',function(d){return d.id!==id});
      fl.filter(function(d){return d.id===id}).raise();place(k0);
      if(nl.lat!=null)svg.interrupt().transition().duration(RM()?0:350).ease(d3.easeCubicOut).call(zoom.transform,focusT(nl));
      return true;
    };
  }
  if(detail&&sel&&sel.lat!=null){
    svg.call(zoom.transform,focusT(sel));
  }else if(!detail&&vui.zoom)svg.call(zoom.transform,vui.zoom);
  else place(1);
  if(!detail)vui.resetZoom=function(){svg.transition().duration(350).call(zoom.transform,d3.zoomIdentity)};
  if(detail&&sel&&sel.lat==null)d3.select(el).append('p').attr('class','hint vml nopos').text('Für diesen Lead ist noch keine Kartenposition bekannt.');
}

/* Lead-Detail */
function vrow(k,v){return v?'<tr><td>'+k+'</td><td>'+v+'</td></tr>':''}
function renderLead(keep){
  var d=$('#detail'),l=lead(ui.lead);
  if(!l){d.hidden=true;d.innerHTML='';return}
  var ae=document.activeElement;
  if(keep&&ae&&d.contains(ae)&&/^(INPUT|TEXTAREA|SELECT)$/.test(ae.tagName)){var hc=$('#lhist',d);if(hc)hc.innerHTML=histHtml(l);return}
  var old=$('.dbody',d),st=keep&&old?old.scrollTop:0,s=l.st,max=vMax();
  var telh=String(l.phone||'').replace(/[^\d+]/g,''),tel2=String(l.phone2||'').replace(/[^\d+]/g,'');
  var q=encodeURIComponent(String(l.addr||l.ort).replace(/\s*\(.*?\)\s*/g,' ').trim()+', Österreich');
  var links=[['Google Karte','https://www.google.com/maps/search/?api=1&query='+q],['Satellit','https://maps.google.com/maps?q='+q+'&t=k'],['Apple Karten','https://maps.apple.com/?q='+q+'&t=k']];
  var acts=VBTN.map(function(b){return '<button class="vst s-'+b[0]+'" data-act="leadStatus" data-v="'+b[0]+'" aria-pressed="'+(s===b[0])+'">'+(b[0]==='verworfen'?'<i class="ix">✕</i>':b[0]==='beauftragt'?'<i class="ok">✓</i>':'<i class="dot"></i>')+b[1]+'</button>'}).join('');
  var term='';
  if(VDATED.includes(s)){
    var wv=s==='wiedervorlage',changed=l.inviteAt&&l.inviteT&&l.termin&&l.inviteT!==l.termin;
    term='<div class="vterm"><label for="ltermin">'+(wv?'Wiedervorlage am':'Termin')+'</label><input id="ltermin" type="datetime-local" step="900" data-change="leadTermin" value="'+esc(l.termin)+'">'+
      (l.termin?'<a class="btn main wide" data-act="leadOutlook" href="'+esc(outlookUrl(l))+'" target="_blank" rel="noopener">In Outlook eintragen'+(l.email?' &amp; einladen':'')+'</a>':'<p class="hint">Datum und Uhrzeit wählen, dann kann der Termin in Outlook eingetragen werden.</p>')+
      (l.inviteAt?'<p class="hint">'+(changed?'<b style="color:var(--red)">'+(wv?'Datum':'Termin')+' geändert – bitte erneut eintragen. </b>':'')+'Outlook-Einladung geöffnet am '+esc(fmtStamp(l.inviteAt))+' für '+esc(fmtTermin(l.inviteT))+'</p>':'')+'</div>';
  }
  var kNote=l.kOv!=null?'angepasst · Vorschlag war '+esc(fmtK(l.kEst))+' kWp <button class="lnk" data-act="leadKwpReset">Zurück auf Vorschlag</button>':(l.kb?'Schätzung: '+esc(l.kb):'');
  var srcOpts=VSRC.map(function(x){return '<option value="'+x[0]+'"'+(l.src===x[0]?' selected':'')+'>'+x[1]+'</option>'}).join('')+(VSRC.some(function(x){return x[0]===l.src})?'':'<option value="'+esc(l.src)+'" selected>'+esc(l.src)+'</option>');
  var mapSig=l.id+'|'+l.st+'|'+l.k+'|'+vui.prism+'|'+l.lat+'|'+l.lon+'|'+(C.leads||[]).length,om=$('#vmapd'),keepMap=om&&om.dataset.sig===mapSig?om:null;
  var mbase=vui.prism+'|'+(C.leads||[]).length;
  if(!keepMap&&om&&om._go&&om.dataset.lid!==l.id&&om.dataset.base===mbase&&om._go(l.id)){keepMap=om;om.dataset.sig=mapSig;om.dataset.lid=l.id}
  if(keepMap)keepMap.parentNode.removeChild(keepMap);
  d.hidden=false;d.classList.add('ldet');
  d.innerHTML='<div class="dmap" id="vmapd-slot"></div><div class="dhead"><button class="x" data-act="closeDetail" aria-label="Zurück zur Übersicht">'+ico.back+'</button><h1>'+esc(l.name)+'</h1></div>'+
  '<div class="dbody">'+
  '<div class="lhead"><span class="lsw big s-'+s+'" style="background:'+leadColor(l,max)+'"><b class="num">'+esc(flagTxt(l))+'</b><small>'+(isPv(l)?'kWp':esc(spLabel(l.sp)))+'</small>'+XSVG+'</span>'+
  '<div class="grow"><div class="lst"><span class="vpill s-'+s+'">'+VST[s]+'</span><span class="tag">'+esc(srcLabel(l.src))+'</span></div><div class="hint">'+(l.stAt?'Status gesetzt am '+esc(fmtStamp(l.stAt)):'Noch kein Status gesetzt')+'</div></div></div>'+
  '<div class="qrow">'+(telh?'<a class="qb" href="tel:'+esc(telh)+'">'+ico.tel+'Anrufen</a>':'')+
    ((l.addr||l.ort)?'<a class="qb" href="https://www.google.com/maps/dir/?api=1&amp;destination='+q+'" target="_blank" rel="noopener">'+ico.nav+'Navigation</a>':'')+
    (l.email?'<a class="qb" href="mailto:'+esc(l.email)+'">'+ico.mail+'E-Mail</a>':'')+'</div>'+
  ((s==='eingang'||s==='spam')?'<div class="sect vassign"><div class="sec"><span>'+(s==='spam'?'Vom Filter als Spam erkannt':'Zuordnen')+'</span></div><div class="vin-a">'+[['pv','Photovoltaik'],['verteiler','Verteiler'],['elektro','Hauselektrik']].map(function(x){return '<button class="chip" data-act="leadAssign" data-v="'+x[0]+'">'+x[1]+'</button>'}).join('')+(s==='eingang'?'<button class="chip ghost" data-act="leadAssign" data-v="spam">Spam</button>':'')+'</div></div>':
  '<div class="sect"><div class="sec"><span>Status</span></div><div class="vacts">'+acts+'</div><p class="hint">Nochmal tippen setzt zurück auf „Rückruf offen“.</p>'+term+
  (s==='beauftragt'&&isOffice()?(l.log.some(function(e){return e.text==='Als Projekt angelegt'})?'<p class="hint" style="margin-top:10px">✓ Als Projekt angelegt – zu finden im Betrieb unter Projekte.</p>':'<button class="btn main wide" data-act="leadToProj" style="margin-top:10px">'+(ui.confirm==='lp'+l.id?'Trotzdem als Projekt anlegen':'Als Projekt anlegen')+'</button>'):'')+'</div>')+
  '<div class="contact">'+
  '<div class="crow"><span style="color:var(--ink2)">'+ico.tel+'</span><div class="grow"><span class="k">Telefon</span><span class="v num">'+esc(l.phone||'nicht erfasst')+'</span></div>'+(telh?'<a href="tel:'+esc(telh)+'">Anrufen</a>':'')+'</div>'+
  (l.phone2?'<div class="crow"><span style="width:22px;flex:none"></span><div class="grow"><span class="k">Weitere Nummer</span><span class="v num">'+esc(l.phone2)+'</span></div>'+(tel2?'<a href="tel:'+esc(tel2)+'">Anrufen</a>':'')+'</div>':'')+
  (l.email?'<div class="crow"><span style="width:22px;flex:none"></span><div class="grow"><span class="k">E-Mail</span><span class="v">'+esc(l.email)+'</span></div><a href="mailto:'+esc(l.email)+'">Schreiben</a></div>':'')+
  '<div class="crow"><span style="color:var(--ink2)">'+ico.pin+'</span><div class="grow"><span class="k">Adresse</span><span class="v">'+esc(l.addr||l.ort||'nicht erfasst')+'</span><span class="vlinks">'+links.map(function(x){return '<a href="'+x[1]+'" target="_blank" rel="noopener">'+x[0]+' ↗</a>'}).join('')+'</span></div></div>'+
  '<div class="crow"><span style="width:22px;flex:none"></span><div class="grow"><span class="k">Anfahrt ab Mödling (geschätzt)</span><span class="v">'+esc(fmtKm(l))+'</span>'+(l.lat==null?'<button class="btn small" data-act="leadLocate" style="margin-top:6px">Position aus Adresse bestimmen</button>':'')+'</div></div>'+
  '</div>'+
  '<div class="sect"><div class="sec"><span>Notizen</span></div><div class="fld"><textarea id="lnote" data-change="leadNote" rows="4" placeholder="Gesprächsinhalt, Rückfragen, Besonderheiten">'+esc(l.notiz)+'</textarea><div class="hint" id="lnote-st">'+(l.notizAt?'Zuletzt gespeichert '+esc(fmtStamp(l.notizAt)):'Wird beim Verlassen des Feldes gespeichert')+'</div></div></div>'+
  '<div class="sect"><div class="sec"><span>Angaben</span><button class="btn small" data-act="leadEdit">Bearbeiten</button></div><table class="kv">'+
  '<tr><td>kWp</td><td><input id="lkwp" type="text" inputmode="decimal" data-change="leadKwp" value="'+(l.k!=null?esc(fmtK(l.k)):'')+'" placeholder="kWp" aria-label="Anlagengröße in kWp"><div class="hint">'+kNote+'</div></td></tr>'+
  '<tr><td>Sparte</td><td><select id="lsp" data-change="leadSparte" aria-label="Sparte">'+VSP.map(function(x){return '<option value="'+x[0]+'"'+(l.sp===x[0]?' selected':'')+'>'+x[1]+'</option>'}).join('')+'</select></td></tr>'+
  '<tr><td>Quelle</td><td><select id="lsrc" data-change="leadSrc" aria-label="Quelle">'+srcOpts+'</select></td></tr>'+
  vrow('CRM-Stand',esc(l.last))+vrow('Eingetragen',esc(l.eingang))+vrow('Anrede',esc(l.anrede))+vrow('Personen',esc(l.personen))+vrow('Stromspeicher',esc(l.speicher))+vrow('Objekt',esc(l.objekt))+vrow('Ausrichtung',esc(l.ausrichtung))+
  vrow('Dach',esc(l.dach))+vrow('Verbrauch',esc(l.verbrauch))+vrow(l.src==='Web'?'Anliegen':'Wünsche',esc(l.wuensche))+vrow('Budget',esc(l.budget))+vrow('Zeitrahmen',esc(l.umsetzung))+vrow(l.src==='Web'?'Nachricht':'Info',esc(l.info))+'</table></div>'+
  '<div class="sect"><div class="sec"><span>Verlauf</span><span class="num">'+(l.log.length+l.hist.length)+'</span></div><ul class="lhist" id="lhist">'+histHtml(l)+'</ul></div>'+
  (isOffice()?'<button class="btn danger wide" data-act="leadDelete">'+(ui.confirm==='ld'+l.id?'Wirklich löschen? Nochmal tippen':'Lead löschen')+'</button>':'')+
  '</div>';
  var nb=$('.dbody',d);if(nb&&st)nb.scrollTop=st;
  var slot=$('#vmapd-slot');
  if(keepMap)slot.parentNode.replaceChild(keepMap,slot);
  else{slot.id='vmapd';slot.dataset.sig=mapSig;slot.dataset.lid=l.id;slot.dataset.base=mbase;slot.innerHTML='<p class="hint vml">Karte wird geladen…</p>';
    loadMapLibs().then(function(){if(slot.isConnected)drawMap(slot,{sel:l.id})}).catch(function(){slot.innerHTML='<p class="hint vml">Karte offline nicht verfügbar.</p>'})}
  var ta=$('#lnote');if(ta)ta.addEventListener('input',function(){var x=$('#lnote-st');if(x)x.textContent='Ungespeicherte Änderung – wird beim Verlassen des Feldes gespeichert'});
}
function histHtml(l){
  var own=l.log.map(function(e){var who=e.by?first(person(e.by).name):(e.byName||'');return '<li><span class="hd">'+esc(fmtStamp(e.at))+(who?' · '+esc(who):'')+'</span>'+esc(e.text)+'</li>'}).join('');
  var src=l.hist.length?'<li class="hsep">aus '+esc(srcLabel(l.src))+':</li>'+l.hist.map(function(x){return '<li class="hsrc">'+esc(x)+'</li>'}).join(''):'';
  return own+src||'<li class="hint">Noch kein Verlauf.</li>';
}
function leadAssign(id,v){
  var l=lead(id);if(!l)return;var now=new Date().toISOString();
  if(v==='spam'){mut('leads','up',{id:id,status:'spam',status_at:now});logLead(id,'Als Spam markiert');toast('„'+l.name+'“ ist im Spam-Ordner');if(ui.lead===id)closeDetailAnimated();return}
  mut('leads','up',{id:id,sparte:v,status:'offen',status_at:now});logLead(id,'Zugeordnet: '+spLabel(v)+' · Rückruf offen');toast('Zugeordnet: '+spLabel(v));
}
function spamHtml(){
  var L=(S.leads||[]).filter(function(l){return l.st==='spam'}).sort(function(a,b){return b.created-a.created});
  if(!L.length)return '<p class="hint">Der Spam-Ordner ist leer.</p>';
  return '<p class="hint">Hier landet, was der Filter als Werbung erkannt hat. Einträge löschen sich nach 30 Tagen selbst.</p>'+L.map(function(l){
    var why=(l.log.filter(function(e){return /Spam/.test(e.text)})[0]||{}).text||'';
    return '<div class="vin"><div class="vin-t"><b>'+esc(l.name)+'</b><span>'+esc(l.email||'')+' · '+esc(fmtStamp(l.created))+'</span><span class="vin-m">'+esc((l.info||'').slice(0,160))+'</span>'+(why?'<span class="vin-m" style="opacity:.7">'+esc(why)+'</span>':'')+'</div>'+
      '<div class="vin-a"><button class="chip" data-act="spamBack" data-id="'+esc(l.id)+'">Kein Spam</button>'+(isOffice()?'<button class="chip ghost" data-act="spamDel" data-id="'+esc(l.id)+'">Löschen</button>':'')+'</div></div>'}).join('');
}
function sheetSpam(){openSheet('spam',sheetShell('Spam','Vom Filter aussortierte Anfragen','<div class="form" id="spamList">'+spamHtml()+'</div>','85%'))}
function sheetSpamKeep(){var x=$('#spamList');if(x)x.innerHTML=spamHtml()}
function leadToProj(id){
  var l=lead(id);if(!l||!isOffice())return;
  var dup=(S.projects||[]).filter(function(p){return (l.email&&p.email&&p.email.toLowerCase()===l.email.toLowerCase())||(l.phone&&p.phone&&p.phone.replace(/\D/g,'').slice(-8)===l.phone.replace(/\D/g,'').slice(-8))})[0];
  if(dup&&ui.confirm!=='lp'+id){ui.confirm='lp'+id;renderLead(true);toast('Es gibt schon ein Projekt „'+dup.name+'“ – nochmal tippen legt trotzdem an');return}
  ui.confirm=null;
  var p={id:uuid(),kundennr:null,name:l.name,short:l.short||shortOf(l.name),addr:l.addr||l.ort||'',phone:l.phone||null,phone2:l.phone2||null,email:l.email||null,
    note:'Aus dem Vertrieb übernommen ('+spLabel(l.sp)+', '+new Date().toLocaleDateString('de-AT')+')'+(l.notiz?'\n'+l.notiz:''),termin:null,status:'aktiv',created_at:new Date().toISOString()};
  mut('projects','up',p);logLead(id,'Als Projekt angelegt');toast('Projekt „'+l.name+'“ angelegt');
}
/* Übergänge: Karte gleitet aus der Übersicht in den Streifen und zurück (nur transform/opacity) */
var EASE_D='cubic-bezier(0.32,0.72,0,1)';
function visRect(el){
  if(!el)return null;var r=el.getBoundingClientRect(),m=$('#main').getBoundingClientRect();
  var vis=Math.min(r.bottom,m.bottom)-Math.max(r.top,m.top);return r.width&&vis>r.height*0.5?r:null;
}
function flipT(a,b){return 'translate('+(a.left-b.left)+'px,'+(a.top-b.top)+'px) scale('+(a.width/b.width)+','+(a.height/b.height)+')'}
function flipIn(from){
  var d=$('#detail'),dm=$('#vmapd',d);if(!dm)return;var to=dm.getBoundingClientRect();if(!to.width)return;
  dm.animate([{transformOrigin:'0 0',transform:flipT(from,to)},{transformOrigin:'0 0',transform:'none'}],{duration:260,easing:EASE_D});
  [$('.dhead',d),$('.dbody',d)].forEach(function(x){if(x)x.animate([{opacity:0,transform:'translateY(12px)'},{opacity:1,transform:'none'}],{duration:220,delay:70,easing:EASE_D,fill:'backwards'})});
}
function openLead(id){
  if(ui.sheetKind)closeSheet();ui.confirm=null;
  var d=$('#detail'),from=(!ui.lead&&!ui.detail&&ui.tab==='vertrieb'&&!RM()&&d.animate)?visRect($('#vmap')):null;
  d.classList.toggle('flip',!!from);
  ui.lead=id;ui.detail=null;renderLead();var b=$('#detail .dbody');if(b)b.scrollTop=0;
  if(from)flipIn(from);
}
function closeDetailAnimated(){
  var d=$('#detail'),wasLead=!!ui.lead;
  ui.confirm=null;ui.detail=null;ui.lead=null;
  if(d.hidden||RM()||!d.animate){renderDetail();refresh();return}
  var to=wasLead&&ui.tab==='vertrieb'?visRect($('#vmap')):null,dm=$('#vmapd',d),an=[],dur=200;
  d.style.pointerEvents='none';
  if(to&&dm){
    dur=250;var fr=dm.getBoundingClientRect();
    an.push(dm.animate([{transformOrigin:'0 0',transform:'none'},{transformOrigin:'0 0',transform:flipT(to,fr)}],{duration:dur,easing:EASE_D,fill:'forwards'}));
    an.push(d.animate([{backgroundColor:getComputedStyle(d).backgroundColor},{backgroundColor:'rgba(0,0,0,0)'}],{duration:dur,easing:'ease-out',fill:'forwards'}));
    [$('.dhead',d),$('.dbody',d)].forEach(function(x){if(x)an.push(x.animate([{opacity:1,transform:'none'},{opacity:0,transform:'translateY(12px)'}],{duration:160,easing:'ease-in',fill:'forwards'}))});
  }else{
    an.push(d.animate([{opacity:1,transform:'none'},{opacity:0,transform:'translateX(60%)'}],{duration:dur,easing:'cubic-bezier(0.4,0,1,1)',fill:'forwards'}));
  }
  setTimeout(function(){
    d.style.pointerEvents='';
    if(!ui.detail&&!ui.lead){renderDetail();an.forEach(function(a){try{a.cancel()}catch(e){}})}
    else an.forEach(function(a){try{a.cancel()}catch(e){}});
    refresh();
  },dur+10);
}
function logLead(id,text){mut('lead_log','up',{id:uuid(),lead_id:id,text:text,at:new Date().toISOString(),created_by:ME.id,by_name:null})}
function setLeadStatus(id,s){
  var l=lead(id);if(!l)return;
  var next=l.st===s?'offen':s,row={id:id,status:next,status_at:new Date().toISOString()};
  if(next!=='einplanen'||!VDATED.includes(l.st)){if(next!==l.st){row.termin=null;row.invite_at=null;row.invite_termin=null}}
  mut('leads','up',row);logLead(id,'Status: '+VST[l.st]+' → '+VST[next]);
  if(next==='einplanen'||next==='wiedervorlage')setTimeout(function(){var i=$('#ltermin');if(i&&!i.value)i.focus()},120);
}
function addMinutes(v,mins){var x=new Date(v);x.setMinutes(x.getMinutes()+mins);return iso(x)+'T'+pad(x.getHours())+':'+pad(x.getMinutes())}
function outlookUrl(l){
  var wv=l.st==='wiedervorlage',n=l.name.replace(/\s*\(.*\)\s*/,'').trim(),adr=String(l.addr||'').replace(/\s*\(.*?\)\s*/g,' ').trim();
  var kontakt='KONTAKT\n'+n+'\nTelefon: '+(l.phone||'–')+'\nE-Mail: '+(l.email||'–')+'\nAdresse: '+(adr||'–');
  var sig='\n\nLiebe Grüße\nIhr strom-macher Team\npv@strom-macher.at\n+43 664 11 09 721';
  var p={
    subject:wv?'Wiedervorlage – PV-Projekt nachfragen: '+n:'PV-Termin '+n,
    body:wv?'Vielen Dank '+(l.anrede||n)+' für das nette Gespräch – wir haben uns einen Termin für ein erneutes Gespräch vorgemerkt.'+sig+'\n\n\n'+kontakt:kontakt+'\n\nTermin: Beratung und Vor-Ort-Besichtigung für Ihre Photovoltaikanlage.'+sig,
    startdt:l.termin+':00',enddt:addMinutes(l.termin,wv?30:60)+':00',
    location:wv?'Telefon '+(l.phone||''):adr+(l.phone?' · Tel. '+l.phone:'')
  };
  if(l.email)p.to=l.email;
  return 'https://outlook.office.com/calendar/0/deeplink/compose?'+Object.keys(p).map(function(k){return k+'='+encodeURIComponent(p[k])}).join('&');
}
var vchange={
  leadTermin:function(el){var l=lead(ui.lead);if(!l)return;var v=el.value||null;el.blur();if((v||'')===l.termin)return;mut('leads','up',{id:l.id,termin:v});logLead(l.id,(l.st==='wiedervorlage'?'Wiedervorlage':'Termin')+(v?' gesetzt: '+fmtTermin(v):' entfernt'))},
  leadNote:function(el){var l=lead(ui.lead);if(!l)return;var t=String(el.value||'').replace(/\s+$/,'');if(t===l.notiz)return;var now=new Date().toISOString();
    mut('leads','up',{id:l.id,notiz:t||null,notiz_at:t?now:null});logLead(l.id,t?'Notiz: '+t.replace(/\s+/g,' ').slice(0,200)+(t.length>200?'…':''):'Notiz gelöscht');var x=$('#lnote-st');if(x)x.textContent='Gespeichert'},
  leadKwp:function(el){var l=lead(ui.lead);if(!l)return;var raw=String(el.value).trim(),n=parseFloat(raw.replace(',','.'));
    var nv=(!raw||!isFinite(n)||n<=0)?null:Math.round(n*10)/10;if(nv!=null&&l.kEst!=null&&nv===l.kEst)nv=null;if(nv===l.kOv)return;
    mut('leads','up',{id:l.id,kwp:nv});logLead(l.id,nv==null?'kWp zurück auf Vorschlag ('+fmtK(l.kEst)+')':'kWp geändert: '+fmtK(l.k)+' → '+fmtK(nv))},
  leadSparte:function(el){var l=lead(ui.lead);if(!l||el.value===l.sp)return;el.blur();mut('leads','up',{id:l.id,sparte:el.value});logLead(l.id,'Sparte: '+spLabel(l.sp)+' → '+spLabel(el.value))},
  leadSrc:function(el){var l=lead(ui.lead);if(!l||el.value===l.src)return;el.blur();mut('leads','up',{id:l.id,source:el.value});logLead(l.id,'Quelle: '+srcLabel(l.src)+' → '+srcLabel(el.value))}
};

/* Neuer Lead / Bearbeiten */
var LF=[['lf_name','name','Name','text','Vor- und Nachname',1],['lf_anrede','anrede','Anrede','text','z. B. Frau Muster',1],['lf_phone','phone','Telefon','tel','',1],['lf_email','email','E-Mail','email','',1],
  ['lf_addr','addr','Adresse','text','Straße Nr, PLZ Ort',1],['lf_ort','ort','Ort','text','',1],['lf_kwp','kwp_est','kWp geschätzt','text','z. B. 8',1],
  ['lf_phone2','phone2','Weitere Nummer','tel','',0],['lf_objekt','objekt','Objekt / Dach','text','z. B. Einfamilienhaus, Satteldach Ziegel',0],['lf_aus','ausrichtung','Ausrichtung','text','',0],['lf_dach','dach','Dachfläche','text','',0],
  ['lf_verbrauch','verbrauch','Verbrauch','text','z. B. 6.000 kWh/a',0],['lf_speicher','speicher','Stromspeicher','text','Ja / Nein / Unsicher',0],['lf_w','wuensche','Wünsche','text','Speicher, Wallbox, Notstrom …',0],
  ['lf_bud','budget','Budget','text','',0],['lf_lz','umsetzung','Zeitrahmen','text','',0],['lf_p','personen','Personen im Haushalt','text','',0],['lf_info','info','Info','textarea','',0]];
function sheetLeadForm(l){
  vui.edit=l?l.id:null;vui.geo=l&&l.lat!=null?{lat:l.lat,lon:l.lon,km:l.km,min:l.min,addr:l.addr+'|'+l.ort}:null;
  var src=l?l.src:'SM';vui.src=src;vui.lsp=l?l.sp:'pv';
  var f=function(x){var v=!l?'':x[1]==='kwp_est'?(l.kEst!=null?fmtK(l.kEst):''):(l[x[1]]||'');
    var inp=x[3]==='textarea'?'<textarea id="'+x[0]+'" rows="3">'+esc(v)+'</textarea>':'<input id="'+x[0]+'" type="'+x[3]+'"'+(x[1]==='kwp_est'?' inputmode="decimal"':'')+' autocomplete="off" placeholder="'+esc(x[4])+'" value="'+esc(v)+'">';
    return fld(x[0],x[2],inp)};
  var body='<form class="form" id="frm" data-submit="saveLead" novalidate>'+
    (l?'':'<p class="hint">Tipp: Im Textfeld die Mikrofon-Taste der Handy-Tastatur antippen und diktieren.</p>')+
    LF.filter(function(x){return x[5]}).map(f).join('')+
    '<div class="fld"><label>Sparte</label><div class="chips" id="lf_sp">'+VSP.filter(function(x){return x[0]!=='sonstiges'}).map(function(x){return '<button type="button" class="chip'+(vui.lsp===x[0]?' on':'')+'" data-act="lfSp" data-v="'+x[0]+'">'+x[1]+'</button>'}).join('')+'</div></div>'+
    '<div class="fld"><label>Quelle</label><div class="chips" id="lf_src">'+VSRC.map(function(x){return '<button type="button" class="chip'+(src===x[0]?' on':'')+'" data-act="lfSrc" data-v="'+x[0]+'">'+x[1]+'</button>'}).join('')+'</div></div>'+
    '<div class="fld"><button type="button" class="btn wide" data-act="lfGeo">'+ico.pin+'Position aus Adresse bestimmen</button><div class="hint" id="lf_geo">'+(vui.geo?'Kartenposition vorhanden · ca. '+esc(fmtKm(vui.geo))+' ab Mödling':'Noch keine Kartenposition. Wird beim Speichern automatisch gesucht, wenn Empfang da ist.')+'</div></div>'+
    '<details class="more"'+(l?' open':'')+'><summary>Weitere Angaben</summary><div class="form" style="margin-top:12px">'+LF.filter(function(x){return !x[5]}).map(f).join('')+'</div></details>'+
    '<button class="btn main wide" type="submit" id="lf_save">'+(l?'Änderungen speichern':'Lead anlegen')+'</button></form>';
  vui.src=src;
  openSheet('leadForm',sheetShell(l?'Lead bearbeiten':'Neuer Lead',l?l.name:'',body,'90%'));
  if(!l&&matchMedia('(hover:hover)').matches){var i=$('#lf_name');if(i)i.focus()}
}
async function geocode(addr){
  var q=String(addr||'').replace(/\s*\(.*?\)\s*/g,' ').trim();if(!q)return null;
  var r=await fetch('https://photon.komoot.io/api/?limit=1&lang=de&bbox=9.5,46.3,17.2,49.1&q='+encodeURIComponent(q+', Österreich'));
  if(!r.ok)throw new Error('Adresssuche nicht erreichbar');
  var j=await r.json(),ft=j&&j.features&&j.features[0];if(!ft)return null;
  var c=ft.geometry.coordinates,p=ft.properties||{},d=kmFrom(c[1],c[0]);
  return {lat:Math.round(c[1]*10000)/10000,lon:Math.round(c[0]*10000)/10000,km:d.km,min:d.min,label:[p.street&&(p.street+(p.housenumber?' '+p.housenumber:'')),[p.postcode,p.city||p.name].filter(Boolean).join(' ')].filter(Boolean).join(', ')};
}
async function lfGeo(){
  var a=val('lf_addr'),o=val('lf_ort'),h=$('#lf_geo');if(!a&&!o){setErr('lf_addr','Bitte zuerst eine Adresse oder einen Ort eingeben.');return}setErr('lf_addr','');
  if(!navigator.onLine){h.textContent='Kein Empfang – die Position wird später bestimmt.';return}
  h.textContent='Wird gesucht …';
  try{var g=await geocode(a||o)||(a&&o?await geocode(o):null);
    if(!g){h.textContent='Adresse nicht gefunden. Bitte Schreibweise prüfen oder nur PLZ und Ort eingeben.';return}
    vui.geo=Object.assign(g,{addr:a+'|'+o});h.textContent='Gefunden: '+(g.label||'Position')+' · ca. '+fmtKm(g)+' ab Mödling';
  }catch(e){h.textContent='Adresssuche gerade nicht erreichbar. Der Lead kann trotzdem gespeichert werden.'}
}
async function submitLead(){
  if(vui.busy)return;
  var row={},l=vui.edit?lead(vui.edit):null;
  LF.forEach(function(x){row[x[1]]=nz(val(x[0]))});
  if(!row.name&&!row.phone){setErr('lf_name','Bitte mindestens Name oder Telefon angeben.');return}setErr('lf_name','');
  var k=row.kwp_est!=null?parseFloat(String(row.kwp_est).replace(',','.')):NaN;row.kwp_est=isFinite(k)&&k>0?Math.round(k*10)/10:null;
  row.source=vui.src||'SM';row.sparte=vui.lsp||'pv';row.name=row.name||'Unbekannt';row.short=shortOf(row.name);
  var addrKey=(row.addr||'')+'|'+(row.ort||'');
  if((row.addr||row.ort)&&(!vui.geo||vui.geo.addr!==addrKey)&&navigator.onLine){
    vui.busy=true;var b=$('#lf_save');if(b){b.disabled=true;b.textContent='Position wird bestimmt …'}
    try{var g=await geocode(row.addr||row.ort)||(row.addr&&row.ort?await geocode(row.ort):null);vui.geo=g?Object.assign(g,{addr:addrKey}):null}catch(e){vui.geo=null}
    vui.busy=false;
  }else if(!(row.addr||row.ort))vui.geo=null;
  var g2=vui.geo&&vui.geo.addr===addrKey?vui.geo:null;
  row.lat=g2?g2.lat:null;row.lon=g2?g2.lon:null;row.km=g2?g2.km:null;row.min=g2?g2.min:null;
  if(l){
    var labels={};LF.forEach(function(x){labels[x[1]]=x[2]});
    var map={name:'name',anrede:'anrede',phone:'phone',email:'email',addr:'addr',ort:'ort',kwp_est:'kEst',phone2:'phone2',objekt:'objekt',ausrichtung:'ausrichtung',dach:'dach',verbrauch:'verbrauch',speicher:'speicher',wuensche:'wuensche',budget:'budget',umsetzung:'umsetzung',personen:'personen',info:'info'};
    var ch=Object.keys(map).filter(function(c){var a=l[map[c]],b=row[c];return String(a==null?'':a)!==String(b==null?'':b)}).map(function(c){return labels[c]});
    if(row.source!==l.src)ch.push('Quelle');
    if(row.sparte!==l.sp)ch.push('Sparte');
    if(l.lat!==row.lat||l.lon!==row.lon)ch.push('Kartenposition');
    closeSheet();
    if(!ch.length){toast('Keine Änderungen');return}
    row.id=l.id;mut('leads','up',row);logLead(l.id,'Angaben geändert: '+ch.join(', '));toast('Gespeichert');
    return;
  }
  var slug=String(row.name).toLowerCase().normalize('NFD').replace(/[̀-ͯ]/g,'').replace(/[^a-z0-9]+/g,'-').replace(/^-|-$/g,'').slice(0,30)||'lead';
  row.id='n-'+slug+'-'+Date.now().toString(36);row.status='offen';row.eingang=new Date().toLocaleDateString('de-AT');row.src_hist=[];
  row.created_at=new Date().toISOString();row.created_by=ME.id;
  closeSheet();mut('leads','up',row);logLead(row.id,'Lead angelegt ('+srcLabel(row.source)+')');
  toast(row.lat==null&&(row.addr||row.ort)?'Lead angelegt – Position wird bestimmt, sobald Empfang da ist':'Lead angelegt');
  openLead(row.id);
}
async function leadLocate(){
  var l=lead(ui.lead);if(!l)return;if(!navigator.onLine){toast('Kein Empfang – bitte später erneut versuchen');return}
  try{var g=await geocode(l.addr||l.ort)||(l.addr&&l.ort?await geocode(l.ort):null);
    if(!g){toast('Adresse nicht gefunden – bitte unter „Bearbeiten“ prüfen');return}
    mut('leads','up',{id:l.id,lat:g.lat,lon:g.lon,km:g.km,min:g.min});logLead(l.id,'Kartenposition bestimmt ('+fmtKm(g)+')');toast('Position gefunden');
  }catch(e){toast('Adresssuche gerade nicht erreichbar')}
}
/* Leads ohne Position nachträglich verorten, sobald Empfang da ist (z. B. offline angelegt) */
var vgeoRunning=false;
async function geoPending(){
  if(vgeoRunning||!navigator.onLine||!S.leads)return;vgeoRunning=true;
  try{var todo=S.leads.filter(function(l){return l.lat==null&&(l.addr||l.ort)&&!l.geoTried&&Date.now()-l.created<7*864e5}).slice(0,3);
    for(var i=0;i<todo.length;i++){var l=todo[i];l.geoTried=true;try{var g=await geocode(l.addr||l.ort);if(g)mut('leads','up',{id:l.id,lat:g.lat,lon:g.lon,km:g.km,min:g.min})}catch(e){break}}
  }finally{vgeoRunning=false}
}

/* Snapshot: Karte und Liste als A4-Bild */
async function vSnapshot(btn){
  var node=$('#vcap');if(!node)return;
  btn.disabled=true;var lab=btn.textContent;btn.textContent='Bild wird erstellt …';
  try{
    await loadScript('vendor/html-to-image.min.js');
    var hd=$('.vshot-h',node);if(hd)hd.hidden=false;
    var bg=getComputedStyle(document.documentElement).getPropertyValue('--bg').trim()||'#EDF1F0';
    var raw=await htmlToImage.toCanvas(node,{pixelRatio:2,backgroundColor:bg,filter:function(n){return !(n.classList&&n.classList.contains('noshot'))}});
    if(hd)hd.hidden=true;
    var land=raw.width>raw.height*1.2,PW=land?3508:2480,PH=land?2480:3508,M=120;
    var c=document.createElement('canvas');c.width=PW;c.height=PH;var g=c.getContext('2d');g.fillStyle='#ffffff';g.fillRect(0,0,PW,PH);
    var sc=Math.min((PW-2*M)/raw.width,(PH-2*M)/raw.height),w=raw.width*sc,h=raw.height*sc;g.imageSmoothingQuality='high';g.drawImage(raw,(PW-w)/2,M,w,h);
    var blob=await new Promise(function(res,rej){c.toBlob(function(b){b?res(b):rej(new Error('Bild leer'))},'image/png')});
    var n=new Date();saveFile(blob,'PV-Lead-Karte_'+iso(n)+'_'+pad(n.getHours())+pad(n.getMinutes())+'.png','image/png');
  }catch(e){toast('Snapshot fehlgeschlagen')}
  finally{var h2=$('.vshot-h');if(h2)h2.hidden=true;btn.disabled=false;btn.textContent=lab}
}

Object.assign(actions,{
  openLead:function(el){openLead(el.dataset.id)},
  leadNew:function(){sheetLeadForm(null)},
  leadEdit:function(){var l=lead(ui.lead);if(l)sheetLeadForm(l)},
  leadStatus:function(el){setLeadStatus(ui.lead,el.dataset.v)},
  leadOutlook:function(){var l=lead(ui.lead);if(!l)return;mut('leads','up',{id:l.id,invite_at:new Date().toISOString(),invite_termin:l.termin});
    logLead(l.id,(l.st==='wiedervorlage'?'Wiedervorlage':'Termin')+' in Outlook geöffnet für '+fmtTermin(l.termin)+(l.email?' (Einladung an '+l.email+')':''))},
  leadKwpReset:function(){var l=lead(ui.lead);if(!l||l.kOv==null)return;mut('leads','up',{id:l.id,kwp:null});logLead(l.id,'kWp zurück auf Vorschlag ('+fmtK(l.kEst)+')')},
  leadLocate:leadLocate,
  leadDelete:function(){
    var l=lead(ui.lead);if(!l)return;
    if(ui.confirm!=='ld'+l.id){ui.confirm='ld'+l.id;renderLead(true);return}
    ui.confirm=null;ui.lead=null;renderLead();mut('leads','del',{id:l.id});toast('„'+l.name+'“ gelöscht');
  },
  lfSp:function(el){vui.lsp=el.dataset.v;document.querySelectorAll('#lf_sp .chip').forEach(function(b){b.classList.toggle('on',b===el)})},
  lfSrc:function(el){vui.src=el.dataset.v;document.querySelectorAll('#lf_src .chip').forEach(function(b){b.classList.toggle('on',b===el)})},
  lfGeo:lfGeo,
  vPrism:function(){vui.prism=!vui.prism;vui.sig='';renderTab(false)},
  vSp:function(el){vui.sp=el.dataset.v||'';vui.sig='';renderTab(false)},
  leadAssign:function(el){leadAssign(el.dataset.id||ui.lead,el.dataset.v)},
  vSpam:function(){sheetSpam()},
  spamBack:function(el){var l=lead(el.dataset.id);if(!l)return;mut('leads','up',{id:l.id,status:'eingang',status_at:new Date().toISOString()});logLead(l.id,'Kein Spam – zurück in den Eingang');toast('Zurück im Eingang');setTimeout(sheetSpamKeep,0)},
  spamDel:function(el){var l=lead(el.dataset.id);if(!l)return;mut('leads','del',{id:l.id});toast('Gelöscht');setTimeout(sheetSpamKeep,0)},
  leadToProj:function(){leadToProj(ui.lead)},
  vArch:function(){vui.arch=!vui.arch;vui.sig='';renderTab(false)},
  vReset:function(){if(vui.resetZoom)vui.resetZoom();vui.zoom=null},
  vSnap:function(el){vSnapshot(el)}
});
submits.saveLead=submitLead;

/* ---------- Start ---------- */
async function boot(){
  showAuth('boot');
  await idb.open();
  var c=await idb.get('C'),ob=await idb.get('OB');
  if(c)C=Object.assign(emptyC(),c);
  if(ob&&ob.length)OB=ob;
  build();
  if(!window.supabase||!CFG.url){showAuth('login','Die App ist nicht richtig eingerichtet.');return}
  var hashType=(/[#&]type=(invite|recovery)/.exec(location.hash)||[])[1]||'';
  sb=supabase.createClient(CFG.url,CFG.key,{auth:{persistSession:true,autoRefreshToken:true,detectSessionInUrl:true,storageKey:'sm-auth'}});
  sb.auth.onAuthStateChange(function(ev,sess){
    setTimeout(function(){
      if(ev==='PASSWORD_RECOVERY'){SESSION=sess;showAuth('setpw');return}
      if(ev==='TOKEN_REFRESHED'||ev==='SIGNED_IN'){if(sess)SESSION=sess;return}
      if(ev==='SIGNED_OUT'&&ui.view==='app'&&navigator.onLine){SESSION=null;showAuth('login','Bitte melde dich erneut an.')}
    },0);
  });
  var r;try{r=await sb.auth.getSession()}catch(e){r=null}
  SESSION=r&&r.data&&r.data.session||null;
  if(hashType&&SESSION){showAuth('setpw');return}
  if(SESSION){
    if(C.me&&C.me.id!==SESSION.user.id){C=emptyC();OB=[];await idb.clear();build()}
    if(C.me&&!C.me.missing&&C.me.active!==false){showApp();sync()}
    else{await sync();route()}
  }else{
    if(C.me&&!navigator.onLine&&C.me.active!==false){showApp()}
    else showAuth('login');
  }
}
window.addEventListener('online',function(){setStatus();sync()});
window.addEventListener('offline',setStatus);
document.addEventListener('visibilitychange',function(){if(!document.hidden&&ui.view==='app'){sync();if(typeof renderBubbles==='function')renderTab(false)}});
setInterval(function(){if(!document.hidden&&ui.view==='app')sync()},90000);

if('serviceWorker' in navigator){
  var hadCtl=!!navigator.serviceWorker.controller;
  navigator.serviceWorker.register('sw.js').catch(function(){});
  navigator.serviceWorker.addEventListener('controllerchange',function(){if(hadCtl&&!ui.sheetKind&&ui.view==='app')location.reload();hadCtl=true});
}
boot();

/* ---------- Export-Menü und druckfertige Excel-Dateien ---------- */
var XL='vendor/exceljs.min.js';
var XMIME='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet';

function expProjRows(q){
  q=String(q||'').toLowerCase().trim();
  var words=q.split(/\s+/).filter(Boolean);
  var last=function(p){var m=0;p.hours.forEach(function(h){if(h.at>m)m=h.at});p.mat.forEach(function(b){if(b.at>m)m=b.at});return m};
  var list=S.projects.filter(function(p){var s=(p.name+' '+p.addr+' '+p.kundennr).toLowerCase();return words.every(function(w){return s.indexOf(w)>-1})});
  list=list.map(function(p){return {p:p,l:last(p)}}).sort(function(a,b){return q?a.p.name.localeCompare(b.p.name,'de'):(b.l-a.l)||a.p.name.localeCompare(b.p.name,'de')});
  var total=list.length;list=list.slice(0,30);
  if(!total)return '<p class="hint">Kein Projekt gefunden.</p>';
  return list.map(function(x){
    var p=x.p,h=hoursTotal(p),n=p.mat.length;
    return '<button class="item" data-act="expProj" data-id="'+p.id+'"><span class="grow"><span class="t">'+esc(p.name)+(p.status!=='aktiv'?' <span class="tag">Archiv</span>':'')+'</span><span class="s">'+esc((p.kundennr?p.kundennr+' · ':'')+city(p.addr))+'</span></span><span class="r num" style="font-size:14px">'+(h||n?nf(h)+' h · '+n+' Mat.':'leer')+'</span></button>';
  }).join('')+(total>30?'<p class="hint" style="padding:10px 2px">'+(total-30)+' weitere – Suche eingrenzen.</p>':'');
}
function sheetExport(){
  var e=ui.exp=ui.exp||{loc:'all',zero:false};
  var locs=[{k:'all',n:'Alle Orte'}].concat(LOCS).map(function(l){return '<button type="button" class="chip'+(e.loc===l.k?' on':'')+'" data-act="expLoc" data-v="'+l.k+'">'+l.n+'</button>'}).join('');
  var body='<div class="form" style="gap:22px">'+
    '<div class="form" style="gap:10px"><div class="sec">Lagerliste zum Ausdrucken</div><p class="hint">Welches Material wo liegt und wie viel davon da ist. Pro Lagerort mit Spalte „Gezählt“ für die Inventur.</p>'+
      '<div class="chips" id="expLocs">'+locs+'</div>'+
      '<button type="button" class="chip'+(e.zero?' on':'')+'" id="expZero" data-act="expZero" style="align-self:flex-start">'+(e.zero?'✓ ':'')+'Auch Material ohne Bestand</button>'+
      '<button class="btn main wide" data-act="expLager">Lagerliste erstellen</button></div>'+
    '<div class="form" style="gap:10px"><div class="sec">Projekt-Aufmaß</div><p class="hint">Stunden und gebuchtes Material eines Projekts – Projekt antippen.</p>'+
      '<div class="fld"><input id="eq" type="search" data-filter="expproj" placeholder="Name, Ort oder Kundennummer" aria-label="Projekt suchen" autocomplete="off"></div>'+
      '<div class="list" id="elist">'+expProjRows('')+'</div></div>'+
    '<div class="form" style="gap:10px"><div class="sec">Gesamtexport</div><p class="hint">Alle Daten in einer Datei (Projekte, Stunden, Material, Lager, Lieferungen, Umbuchungen, Aufgaben) – zum Weiterverarbeiten, nicht zum Drucken.</p>'+
      '<button class="btn wide" data-act="export">Gesamtexport erstellen</button></div>'+
    '</div>';
  openSheet('export',sheetShell('Export & Ausdrucke','Excel-Dateien erstellen',body,'92%'));
  loadScript(XL).catch(function(){});loadScript('vendor/xlsx.full.min.js').catch(function(){});
}

/* Hilfen für ExcelJS */
async function xlBook(){
  try{await loadScript(XL)}catch(e){toast('Der Excel-Export konnte nicht geladen werden. Bitte einmal online öffnen.');return null}
  var wb=new ExcelJS.Workbook();wb.creator='strom-macher App';wb.created=new Date();return wb;
}
var XB={style:'thin',color:{argb:'FFB4BDBB'}};
function xlBox(c){c.border={top:XB,left:XB,bottom:XB,right:XB}}
function xlHeadRow(r){r.height=22;r.eachCell(function(c){c.font={bold:true};c.fill={type:'pattern',pattern:'solid',fgColor:{argb:'FFE3ECEA'}};xlBox(c);c.alignment={vertical:'middle',wrapText:true}})}
function xlBodyRow(r,i,n){r.eachCell({includeEmpty:true},function(c,col){if(col>n)return;xlBox(c);c.alignment=Object.assign({vertical:'top',wrapText:true},c.alignment||{});if(i%2)c.fill={type:'pattern',pattern:'solid',fgColor:{argb:'FFF6F8F7'}}})}
function xlPage(ws,land,titles){
  ws.pageSetup={paperSize:9,orientation:land?'landscape':'portrait',fitToPage:true,fitToWidth:1,fitToHeight:0,horizontalCentered:true,
    margins:{left:0.5,right:0.5,top:0.6,bottom:0.7,header:0.3,footer:0.3}};
  if(titles)ws.pageSetup.printTitlesRow=titles;
  ws.headerFooter={oddFooter:'&L&8strom-macher&C&8Seite &P von &N&R&8'+stamp()};
}
function stamp(){var d=new Date(),z=function(n){return (n<10?'0':'')+n};return z(d.getDate())+'.'+z(d.getMonth()+1)+'.'+d.getFullYear()+' '+z(d.getHours())+':'+z(d.getMinutes())}
/* Excel kennt keine Zeitzonen: Ortszeit als „UTC“ ablegen, damit die Uhrzeit stimmt */
function xd(ms){var d=new Date(ms);return new Date(ms-d.getTimezoneOffset()*60000)}
function xday(s){return xd(new Date(s+'T12:00').getTime())}
var NUM='#,##0.###';
function fileSafe(s){var m={'ä':'ae','ö':'oe','ü':'ue','Ä':'Ae','Ö':'Oe','Ü':'Ue','ß':'ss'};return String(s||'').replace(/[äöüÄÖÜß]/g,function(c){return m[c]}).replace(/[^\w\- ]+/g,'').trim().replace(/\s+/g,'_').slice(0,40)}
async function xlSave(wb,name){
  var buf=await wb.xlsx.writeBuffer();
  saveFile(new Blob([buf],{type:XMIME}),name,XMIME);
}
function xlTitle(ws,title,sub){
  var r=ws.getRow(1);r.getCell(1).value=title;r.getCell(1).font={bold:true,size:16};r.height=24;
  var r2=ws.getRow(2);r2.getCell(1).value=sub;r2.getCell(1).font={size:10,color:{argb:'FF5C6664'}};
}

/* Lagerliste */
async function exportLager(loc,zero){
  var wb=await xlBook();if(!wb)return;
  var all=loc==='all';
  var ms=S.mats.filter(function(m){return zero||(all?m.stock!==0:m.locs[loc]!==0)}).sort(function(a,b){return a.name.localeCompare(b.name,'de')});
  var ws=wb.addWorksheet(all?'Lagerliste':locName(loc),{views:[{state:'frozen',ySplit:4}]});
  xlTitle(ws,'Lagerliste – '+(all?'alle Lagerorte':locName(loc)),'strom-macher · Stand '+stamp()+' · '+ms.length+' Materialien');
  var head,widths;
  if(all){head=['QR','Material','Einheit'].concat(LOCS.map(function(l){return l.n}),['Gesamt']);widths=[10,52,8,12,10,12,12,10]}
  else{head=['QR','Material','Einheit','Bestand','Gezählt'];widths=[10,56,8,11,11]}
  ws.columns=widths.map(function(w){return {width:w}});
  var hr=ws.getRow(4);hr.values=head;xlHeadRow(hr);
  for(var c=4;c<=head.length;c++)hr.getCell(c).alignment={horizontal:'right',vertical:'middle',wrapText:true};
  ms.forEach(function(m,i){
    var vals=all?[m.qr,m.name,m.unit].concat(LOCK.map(function(k){return m.locs[k]||null}),[m.stock]):[m.qr,m.name,m.unit,m.locs[loc],null];
    var r=ws.getRow(5+i);r.values=vals;
    for(var c=4;c<=head.length;c++)r.getCell(c).numFmt=NUM;
    if(all)r.getCell(head.length).font={bold:true};
    xlBodyRow(r,i,head.length);
  });
  if(!ms.length){ws.getCell('A5').value=zero?'Noch kein Material angelegt.':'An diesem Ort ist derzeit kein Material mit Bestand.'}
  xlPage(ws,all,'4:4');
  await xlSave(wb,'Lagerliste_'+(all?'alle_Orte':fileSafe(locName(loc)))+'_'+TODAY()+'.xlsx');
  toast('Lagerliste erstellt');
}

/* Projekt-Aufmaß zum Ausdrucken */
async function exportProjekt(pid){
  var p=proj(pid);if(!p)return;
  var wb=await xlBook();if(!wb)return;
  var off=isOffice();
  var ws=wb.addWorksheet('Aufmaß');
  ws.columns=[{width:13},{width:40},{width:11},{width:10},{width:24}];
  xlTitle(ws,'Aufmaß','strom-macher · Elektrotechnik & Photovoltaik');
  var row=4;
  function kv(k,v){var r=ws.getRow(row++);r.getCell(1).value=k;r.getCell(1).font={color:{argb:'FF5C6664'}};r.getCell(2).value=v||'';ws.mergeCells(r.number,2,r.number,5);r.getCell(2).alignment={wrapText:true,vertical:'top'};return r}
  kv('Kunde',p.name).getCell(2).font={bold:true,size:12};
  if(p.kundennr)kv('Kundennr.',p.kundennr);
  kv('Adresse',p.addr);
  if(p.phone)kv('Telefon',p.phone+(p.phone2?' · '+p.phone2:''));
  kv('Stand',stamp());
  row++;
  function section(t){var r=ws.getRow(row++);r.getCell(1).value=t;r.getCell(1).font={bold:true,size:12};r.height=20}
  function head(vals,merge){var r=ws.getRow(row++);r.values=vals;if(merge)ws.mergeCells(r.number,4,r.number,5);xlHeadRow(r);return r}

  /* Stunden */
  section('Arbeitsstunden');
  var hr=head(['Datum','Erfasst von','Stunden','Notiz'],true);hr.getCell(3).alignment={horizontal:'right',vertical:'middle'};hr.getCell(4).alignment={vertical:'middle',indent:1};
  var hs=p.hours.slice().sort(function(a,b){return a.date<b.date?-1:a.date>b.date?1:a.at-b.at});
  var per={};
  hs.forEach(function(h,i){
    var nm=person(h.by).name||'';per[nm]=(per[nm]||0)+h.h;
    var r=ws.getRow(row++);r.values=[xday(h.date),nm,h.h,h.note||''];ws.mergeCells(r.number,4,r.number,5);
    r.getCell(1).numFmt='dd.mm.yyyy';r.getCell(3).numFmt=NUM;xlBodyRow(r,i,5);r.getCell(4).alignment={vertical:'top',wrapText:true,indent:1};
  });
  if(!hs.length){var r0=ws.getRow(row++);r0.getCell(1).value='Keine Stunden erfasst.';}
  var sr=ws.getRow(row++);sr.getCell(1).value='Summe Stunden';sr.getCell(3).value=Math.round(hoursTotal(p)*100)/100;sr.getCell(3).numFmt=NUM;
  [1,2,3].forEach(function(c){sr.getCell(c).font={bold:true};sr.getCell(c).border={top:{style:'medium'}}});
  var names=Object.keys(per);
  if(names.length>1){
    row++;var r1=ws.getRow(row++);r1.getCell(1).value='davon erfasst von';r1.getCell(1).font={color:{argb:'FF5C6664'}};
    names.sort().forEach(function(n){var r=ws.getRow(row++);r.getCell(2).value=n;r.getCell(3).value=Math.round(per[n]*100)/100;r.getCell(3).numFmt=NUM});
  }
  row++;

  /* Material, je Material zusammengefasst */
  section('Material');
  var mh=head(['QR','Material','Menge','Einheit']);mh.getCell(3).alignment={horizontal:'right',vertical:'middle'};mh.getCell(4).alignment={vertical:'middle',indent:1};
  var agg={};
  p.mat.forEach(function(b){agg[b.matId]=(agg[b.matId]||0)+b.qty});
  var ids=Object.keys(agg).filter(function(id){return Math.abs(agg[id])>1e-9}).sort(function(a,b){return ((mat(a)||{}).name||'').localeCompare(((mat(b)||{}).name||''),'de')});
  ids.forEach(function(id,i){
    var m=mat(id)||{name:'(gelöschtes Material)',qr:'',unit:''};
    var r=ws.getRow(row++);r.values=[m.qr,m.name,Math.round(agg[id]*1000)/1000,m.unit];r.getCell(3).numFmt=NUM;xlBodyRow(r,i,4);r.getCell(4).alignment={vertical:'top',indent:1};
  });
  if(!ids.length){var r2=ws.getRow(row++);r2.getCell(1).value='Kein Material gebucht.';}

  /* Unterschriften */
  row+=3;
  var ur=ws.getRow(row);
  [1,2].forEach(function(c){ur.getCell(c).border={top:{style:'thin'}}});[4,5].forEach(function(c){ur.getCell(c).border={top:{style:'thin'}}});
  ur.getCell(1).value='Datum, Unterschrift Kunde';ur.getCell(4).value='Datum, Unterschrift strom-macher';
  ur.getCell(1).font=ur.getCell(4).font={size:9,color:{argb:'FF5C6664'}};
  xlPage(ws,false,null);

  /* Blatt 2: einzelne Materialbuchungen (zum Nachschauen, nicht zum Drucken) */
  var w2=wb.addWorksheet('Materialbuchungen',{views:[{state:'frozen',ySplit:1}]});
  var h2=['Datum','Material','QR','Menge','Einheit','Entnommen aus','Gebucht von'].concat(off?['Einkaufspreis €','Wert €']:[]);
  w2.columns=[16,40,10,9,8,14,18,14,10].slice(0,h2.length).map(function(w){return {width:w}});
  var r2h=w2.getRow(1);r2h.values=h2;xlHeadRow(r2h);
  p.mat.slice().sort(function(a,b){return a.at-b.at}).forEach(function(b,i){
    var m=mat(b.matId)||{name:'',qr:'',unit:'',price:0};
    var vals=[xd(b.at),m.name,m.qr,b.qty,m.unit,locName(b.loc),person(b.by).name||''];
    if(off)vals.push(m.price||null,m.price?Math.round(b.qty*m.price*100)/100:null);
    var r=w2.getRow(2+i);r.values=vals;r.getCell(1).numFmt='dd.mm.yyyy hh:mm';r.getCell(4).numFmt=NUM;
    if(off){r.getCell(8).numFmt='#,##0.00';r.getCell(9).numFmt='#,##0.00'}
    xlBodyRow(r,i,h2.length);
  });
  xlPage(w2,true,'1:1');

  await xlSave(wb,'Aufmass_'+(p.kundennr?p.kundennr+'_':'')+(fileSafe(p.name)||'Projekt')+'_'+TODAY()+'.xlsx');
  toast('Aufmaß erstellt');
}
})();
