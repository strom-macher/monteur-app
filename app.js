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
var TABLES=['profiles','projects','tasks','hours','photos','materials','material_costs','stock_moves','delivery_suppliers'];
var COLS={
  profiles:['id','name','role','active'],
  projects:['id','kundennr','name','short','addr','phone','phone2','email','note','termin','status','created_at'],
  tasks:['id','name','project_id','assignee','due','due_time','done','done_at','created_by','created_at'],
  photos:['id','project_id','path','taken_at','created_by'],
  hours:['id','project_id','work_date','h','note','created_by','created_at'],
  materials:['id','name','unit','min_stock','note'],
  material_costs:['material_id','price','supplier','artnr'],
  stock_moves:['id','material_id','project_id','qty','kind','note','created_by','created_at'],
  delivery_suppliers:['move_id','supplier']
};
var PK=function(t){return t==='material_costs'?'material_id':t==='delivery_suppliers'?'move_id':'id'};
function pick(t,row){var o={};COLS[t].forEach(function(c){if(row[c]!==undefined)o[c]=row[c]});return o}
function emptyC(){var c={me:null,pulledAt:0};TABLES.forEach(function(t){c[t]=[]});return c}

var C=emptyC();      /* lokaler Spiegel der Datenbank */
var OB=[];           /* Warteschlange: noch nicht übertragene Änderungen */
var S={projects:[],tasks:[],mats:[]};  /* abgeleitete Sicht für die Oberfläche */
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
  var stock={},dels={},bk={};
  C.stock_moves.forEach(function(m){
    stock[m.material_id]=(stock[m.material_id]||0)+Number(m.qty);
    if(m.kind==='anfang'||m.kind==='lieferung'||(m.kind==='korrektur'&&Number(m.qty)>0))(dels[m.material_id]=dels[m.material_id]||[]).push({id:m.id,date:iso(new Date(msOf(m.created_at))),at:msOf(m.created_at),qty:Number(m.qty),supplier:dsup[m.id]||'',note:m.kind==='anfang'?'Anfangsbestand':(m.note||''),by:m.created_by});
    if(m.kind==='buchung'&&m.project_id)(bk[m.project_id]=bk[m.project_id]||[]).push({id:m.id,matId:m.material_id,qty:-Number(m.qty),at:msOf(m.created_at),by:m.created_by});
  });
  S.mats=C.materials.map(function(m){
    var c=costs[m.id]||{};
    var d=(dels[m.id]||[]).sort(function(a,b){return b.at-a.at});
    return {id:m.id,name:m.name,unit:m.unit||'Stk',min:Number(m.min_stock)||0,note:m.note||'',qr:m.qr||'',
      stock:Math.round((stock[m.id]||0)*1000)/1000,price:Number(c.price)||0,supplier:c.supplier||'',artnr:c.artnr||'',deliveries:d};
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
  tel:'<svg width="22" height="22" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.1" stroke-linejoin="round"><path d="M6.5 3.5h3l1.5 4-2 1.5a11 11 0 005.5 5.5l1.5-2 4 1.5v3a2 2 0 01-2 2A15.5 15.5 0 014.5 5.5a2 2 0 012-2z"/></svg>',
  clock:'<svg width="19" height="19" viewBox="0 0 24 24" fill="none" stroke="#101514" stroke-width="2.3" stroke-linecap="round"><circle cx="12" cy="12" r="8.5"/><path d="M12 7.5V12l3 2"/></svg>',
  box:'<svg width="19" height="19" viewBox="0 0 24 24" fill="none" stroke="#101514" stroke-width="2.3" stroke-linejoin="round"><path d="M12 3l8 4.5v9L12 21l-8-4.5v-9z"/><path d="M4 7.5l8 4.5 8-4.5M12 12v9"/></svg>',
  bolt:'<svg width="20" height="20" viewBox="0 0 24 24" fill="#101514"><path d="M13 2L5 13.5h5.5L9.5 22 19 9.5h-5.8z"/></svg>'
};
/* ---------- Oberfläche ---------- */
var ui={tab:'home',detail:null,sheet:null,pend:{},tm:'active',tf:'all',m:null,h:{val:0},scanNext:null,confirm:null,sheetKind:'',curMat:null};
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
  var more=act.length>5?'<p class="hint" style="text-align:center">'+(act.length-5)+' weitere aktive Aufgaben hinter den drei Punkten</p>':'';
  return '<div class="titlebar rise" style="--i:0"><div class="pill">Aufgaben</div><button class="plus" data-act="addTask" aria-label="Neue Aufgabe">+</button></div>'+
    '<div class="body"><div class="panel rise" style="--i:1">'+rows+'<button class="dots" data-act="allTasks" aria-label="Alle aktiven Aufgaben anzeigen"><span></span><span></span><span></span></button></div>'+more+'</div>';
}
function tabLager(){
  var low=S.mats.filter(isLow).sort(function(a,b){return a.stock/a.min-b.stock/b.min});
  var lowHtml=low.length?'<div class="lowbox rise" style="--i:3"><div class="sec"><span>Unter Mindestbestand</span><span class="tag red">'+low.length+'</span></div><div class="list">'+low.slice(0,3).map(function(m){
      return '<button class="item" data-act="openMat" data-id="'+m.id+'"><span class="grow"><span class="t">'+esc(m.name)+'</span><span class="s">Mindestbestand '+nf(m.min,0)+' '+esc(m.unit)+'</span></span><span class="r num" style="color:var(--red)">'+nf(m.stock,0)+' '+esc(m.unit)+'</span></button>'}).join('')+'</div></div>'
    :'<p class="hint rise" style="--i:3">'+(S.mats.length?'Alle Bestände liegen über dem Mindestbestand.':(isOffice()?'Noch kein Material im Lager. Lege mit „Material anlegen“ das erste an.':'Noch kein Material im Lager.'))+'</p>';
  return '<div class="titlebar rise" style="--i:0"><div class="pill">Lager</div><button class="plus" data-act="delivery" aria-label="Lieferung verbuchen">+</button></div>'+
    '<div class="body">'+(isOffice()?'<button class="btn main wide rise" style="--i:1" data-act="newMat">Material anlegen</button>':'')+
    '<div class="row2 rise" style="--i:2"><button class="btn" data-act="matSearch">'+ico.search+'Suchen</button><button class="btn" data-act="scan" data-next="detail">'+ico.qr+'Scannen</button></div>'+lowHtml+'</div>';
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
  var h=ui.tab==='home'?tabHome():ui.tab==='lager'?tabLager():ui.tab==='projekte'?tabProjekte():tabAufgaben();
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
  var d=$('#detail'),p=proj(ui.detail);
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
    return '<div class="bk"><span class="bi m">'+ico.box+'</span><div class="grow"><div class="t">'+esc(m.name)+'</div><div class="s num">'+nf(b.x.qty,1)+' '+esc(m.unit)+' · '+esc(fmtTs(b.at))+' · '+esc(first(person(b.x.by).name))+'</div></div>'+del('m')+'</div>';
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
  '<div>'+bkHtml+'</div></div>'+
  (off&&!arch?'<button class="btn danger wide" data-act="closeProj" data-id="'+p.id+'">Projekt abschließen</button>':'')+
  '</div>';
  var nb=$('.dbody',d);if(nb&&st)nb.scrollTop=st;
  loadPhotos();
}
function refresh(keep){renderTab(false);renderBubbles();renderHeader();if(ui.detail)renderDetail(keep)}
function afterChange(){
  if(!ME)return;
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
function matRow(m,act){
  return '<button class="item" data-act="'+act+'" data-id="'+m.id+'" data-q="'+esc((m.name+' '+m.artnr+' '+m.supplier+' '+m.qr).toLowerCase())+'"><span class="grow"><span class="t">'+esc(m.name)+'</span><span class="s">'+esc(m.qr||'QR folgt')+(isOffice()&&m.supplier?' · '+esc(m.supplier):'')+'</span></span>'+(isLow(m)?'<span class="rd" title="Unter Mindestbestand"></span>':'')+'<span class="r num">'+nf(m.stock,0)+' '+esc(m.unit)+'</span></button>';
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
  if(st>0)mut('stock_moves','up',{id:uuid(),material_id:id,project_id:null,qty:st,kind:'anfang',note:null,created_by:ME.id,created_at:now});
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
  var dels=m.deliveries.slice(0,4).map(function(d){return '<div class="bk" style="min-height:50px"><div class="grow"><div class="t num">+'+nf(d.qty,1)+' '+esc(m.unit)+'</div><div class="s">'+esc(fmtDate(d.date))+(off&&d.supplier?' · '+esc(d.supplier):'')+(d.note?' · '+esc(d.note):'')+'</div></div></div>'}).join('')||'<p class="hint">Noch keine Lieferung erfasst.</p>';
  var bks=bookingsOfMat(id).slice(0,4).map(function(x){return '<div class="bk" style="min-height:50px"><div class="grow"><div class="t num">−'+nf(x.b.qty,1)+' '+esc(m.unit)+' · '+esc(x.p.name)+'</div><div class="s">'+esc(fmtTs(x.b.at))+'</div></div></div>'}).join('')||'<p class="hint">Noch auf kein Projekt gebucht.</p>';
  var fields=(off?
    '<div class="grid2">'+fld('mu2','Einheit','<input id="mu2" value="'+esc(m.unit)+'">')+fld('mm2','Mindestbestand','<input id="mm2" inputmode="decimal" value="'+esc(String(m.min).replace('.',','))+'">')+'</div>'+
    '<div class="grid2">'+fld('mpr2','Einkaufspreis (€)','<input id="mpr2" inputmode="decimal" value="'+esc(String(m.price||'').replace('.',','))+'">')+fld('mar2','Artikelnr.','<input id="mar2" value="'+esc(m.artnr)+'">')+'</div>'+
    fld('msu2','Lieferant','<input id="msu2" value="'+esc(m.supplier)+'">'):'')+
    fld('mno2','Notiz','<textarea id="mno2" placeholder="Kurze Notiz für das Team">'+esc(m.note)+'</textarea>');
  var body='<div class="form" style="gap:16px"><div><div class="big num" style="color:'+(low?'var(--red)':'var(--ink)')+'">'+nf(m.stock,1)+'<span style="font-size:22px"> '+esc(m.unit)+'</span></div><div class="hint" style="margin:6px 0 8px">'+(m.min?'Mindestbestand '+nf(m.min,1)+' '+esc(m.unit)+(low?' · unterschritten':''):'Kein Mindestbestand festgelegt')+'</div><div class="bar'+(low?' low':'')+'"><i style="transform:scaleX('+ratio.toFixed(3)+')"></i></div></div>'+
    '<div class="row2"><button class="btn main" data-act="delivery" data-id="'+m.id+'">+ Lieferung</button><button class="btn" data-act="qr" data-id="'+m.id+'">'+ico.qr+'QR-Code</button></div>'+
    '<form class="form" data-submit="saveMatEdit" data-id="'+m.id+'" novalidate>'+fields+'<button class="btn wide" type="submit">'+(off?'Änderungen speichern':'Notiz speichern')+'</button></form>'+
    '<div><div class="sec" style="margin-bottom:4px">Letzte Lieferungen</div>'+dels+'</div><div><div class="sec" style="margin-bottom:4px">Letzte Buchungen auf Projekte</div>'+bks+'</div></div>';
  openSheet('matDetail',sheetShell(m.name,(m.qr||'QR folgt')+(off&&m.supplier?' · '+m.supplier:''),body,'50%'));
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
      '<div class="banner" style="flex-direction:row;align-items:center;justify-content:space-between"><div style="min-width:0"><b style="font-family:var(--f-display)">'+esc(mt.name)+'</b><div class="hint num">Bestand '+nf(mt.stock,1)+' '+esc(mt.unit)+'</div></div><button type="button" class="btn small" data-act="unpick">Ändern</button></div>'+
      '<div class="fld" id="f-qty"><label for="qty">Menge ('+esc(mt.unit)+')</label><div class="stepper"><button type="button" class="btn" data-act="qtyStep" data-v="-1" aria-label="Weniger">−</button><input id="qty" type="text" inputmode="decimal" value="'+esc(String(m.qty).replace('.',','))+'"><button type="button" class="btn" data-act="qtyStep" data-v="1" aria-label="Mehr">+</button></div><div class="chips">'+chips+'</div><div class="err" id="e-qty"></div></div>'+
      (book?'':(isOffice()?fld('dsu','Lieferant','<input id="dsu" value="'+esc(mt.supplier)+'">'):'')+fld('dno','Lieferschein (optional)','<input id="dno" autocomplete="off">'))+
      '<button class="btn main wide" type="submit">'+(book?'Auf Projekt buchen':'Lieferung einbuchen')+'</button></form>';
  }
  openSheet('mat',sheetShell(title,sub,body,'50%'));
}
function openMatFlow(mode,pid,sel){ui.m={mode:mode,pid:pid||null,sel:sel||null,qty:1};sheetMat()}
function submitBook(){
  var mt=mat(ui.m.sel),p=proj(ui.m.pid),q=num('qty');
  if(!(q>0)){setErr('qty','Bitte eine Menge über 0 eingeben.');return}
  if(q>mt.stock){setErr('qty','Nur '+nf(mt.stock,1)+' '+mt.unit+' im Lager.');return}
  var was=isLow(mt);
  closeSheet();
  mut('stock_moves','up',{id:uuid(),material_id:mt.id,project_id:p.id,qty:-q,kind:'buchung',note:null,created_by:ME.id,created_at:new Date().toISOString()});
  toast(nf(q,1)+' '+mt.unit+' '+mt.name.split(',')[0]+' gebucht'+(!was&&isLow(mat(mt.id))?' · Mindestbestand unterschritten':''));
}
function submitDelivery(){
  var mt=mat(ui.m.sel),q=num('qty');
  if(!(q>0)){setErr('qty','Bitte eine Menge über 0 eingeben.');return}
  var sup=isOffice()&&$('#dsu')?val('dsu'):'';
  var mid=uuid();
  closeSheet();
  mut('stock_moves','up',{id:mid,material_id:mt.id,project_id:null,qty:q,kind:'lieferung',note:nz(val('dno')),created_by:ME.id,created_at:new Date().toISOString()});
  if(isOffice()&&sup){
    mut('delivery_suppliers','up',{move_id:mid,supplier:sup});
    if(sup!==mt.supplier)mut('material_costs','up',{material_id:mt.id,supplier:sup});
  }
  toast('+'+nf(q,1)+' '+mt.unit+' eingebucht · Bestand '+nf(mat(mt.id).stock,1));
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
  if(isIOS&&f&&navigator.canShare&&navigator.canShare({files:[f]})){navigator.share({files:[f]}).catch(function(){});return}
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
    mrows.push([dt(b.at),p.name,p.kundennr,m.name,m.qr,b.qty,m.unit,isOffice()?m.price||'':'',isOffice()&&m.price?Math.round(b.qty*m.price*100)/100:'',person(b.by).name]);
  })});
  mrows.sort(function(a,b){return b[0]-a[0]});
  sheet('Materialbuchungen',['Datum','Projekt','Kundennr.','Material','QR','Menge','Einheit','Einkaufspreis €','Wert €','Gebucht von'],mrows,[14,28,11,34,10,9,9,14,10,18]);
  sheet('Lager',['QR','Material','Einheit','Bestand','Mindestbestand','Unter Mindestbestand','Einkaufspreis €','Lagerwert €','Lieferant','Artikelnr.','Notiz'],
    S.mats.slice().sort(function(a,b){return a.name.localeCompare(b.name,'de')}).map(function(m){
      return [m.qr,m.name,m.unit,m.stock,m.min,isLow(m)?'Ja':'Nein',m.price||'',m.price?Math.round(m.stock*m.price*100)/100:'',m.supplier,m.artnr,m.note];
    }),[10,36,9,9,14,12,14,12,22,16,30]);
  var drows=[];
  S.mats.forEach(function(m){m.deliveries.forEach(function(d){drows.push([dt(d.at),m.name,m.qr,d.qty,m.unit,d.supplier,d.note,person(d.by).name])})});
  drows.sort(function(a,b){return b[0]-a[0]});
  sheet('Lieferungen',['Datum','Material','QR','Menge','Einheit','Lieferant','Notiz / Lieferschein','Erfasst von'],drows,[14,36,10,9,9,22,26,18]);
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
    (off?'<div><div class="sec" style="margin-bottom:8px">Büro</div><div class="form" style="gap:10px"><button class="btn main wide" data-act="export">Excel-Export</button><button class="btn wide" data-act="team">Team verwalten</button></div><p class="hint" style="margin-top:6px">Der Export enthält Projekte, Stunden, Materialbuchungen, Lager, Lieferungen und Aufgaben.</p></div>':'')+
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
  if(ui.detail){ui.detail=null;renderDetail()}
  if(ui.sheetKind)closeSheet();
  ui.tab=t;renderHeader();renderTab(true);
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
  home:function(){setTab('home')},
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
    ui.detail=el.dataset.id;renderDetail();
  },
  closeDetail:function(){ui.detail=null;renderDetail();refresh()},
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
  pickMat:function(el){ui.m.sel=el.dataset.id;ui.m.qty=1;sheetMat()},
  unpick:function(){ui.m.sel=null;sheetMat()},
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
  saveBook:submitBook,saveDelivery:submitDelivery,saveHours:submitHours,scanManual:submitScanManual,
  login:doLogin,reset:doReset,setpw:doSetPw
};

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
  if(kind==='tp'){var s=$('#tp');if(s)s.innerHTML=projOptions(v,s.value,60);return}
  var n=0;
  document.querySelectorAll('#flist .item').forEach(function(it){var hit=!v||it.dataset.q.indexOf(v)>-1;it.hidden=!hit;if(hit)n++});
  var nr2=$('#nores');if(nr2)nr2.hidden=n>0;
});
document.addEventListener('change',function(e){
  var c=e.target.closest('[data-change]');if(!c)return;
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
  renderHeader();renderTab(true);renderBubbles();
  remind();
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
})();
