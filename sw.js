/* strom-macher Service Worker: App-Dateien offline verfügbar halten */
var V='sm-v2';
var SHELL=['./','index.html','app.css','app.js','config.js','manifest.webmanifest',
  'vendor/supabase.js','vendor/qrcode.js','vendor/html5-qrcode.min.js','vendor/xlsx.full.min.js',
  'fonts/outfit-latin-400-normal.woff2','fonts/outfit-latin-500-normal.woff2','fonts/outfit-latin-600-normal.woff2','fonts/outfit-latin-700-normal.woff2',
  'fonts/ibm-plex-sans-latin-400-normal.woff2','fonts/ibm-plex-sans-latin-500-normal.woff2','fonts/ibm-plex-sans-latin-600-normal.woff2',
  'icons/icon-192.png','icons/icon-512.png','icons/apple-touch-icon.png'];
self.addEventListener('install',function(e){
  e.waitUntil(caches.open(V).then(function(c){return c.addAll(SHELL)}).then(function(){return self.skipWaiting()}));
});
self.addEventListener('activate',function(e){
  e.waitUntil(caches.keys().then(function(ks){return Promise.all(ks.filter(function(k){return k!==V}).map(function(k){return caches.delete(k)}))}).then(function(){return self.clients.claim()}));
});
function fromNetwork(req,ms){
  return new Promise(function(res,rej){
    var t=setTimeout(function(){rej(new Error('timeout'))},ms);
    fetch(req).then(function(r){clearTimeout(t);res(r)},function(e){clearTimeout(t);rej(e)});
  });
}
self.addEventListener('fetch',function(e){
  var req=e.request;
  if(req.method!=='GET')return;
  var u=new URL(req.url);
  if(u.origin!==location.origin)return;
  var code=/\.(html|js|css|webmanifest)$/.test(u.pathname)||u.pathname.endsWith('/');
  if(code){
    /* Programmdateien: zuerst Netz (damit Updates sofort ankommen), sonst Zwischenspeicher */
    e.respondWith(fromNetwork(req,3500).then(function(r){
      if(r&&r.ok){var cp=r.clone();caches.open(V).then(function(c){c.put(req,cp)})}
      return r;
    }).catch(function(){
      return caches.match(req,{ignoreSearch:true}).then(function(m){return m||caches.match('index.html')});
    }));
  }else{
    e.respondWith(caches.match(req).then(function(m){
      return m||fetch(req).then(function(r){
        if(r&&r.ok){var cp=r.clone();caches.open(V).then(function(c){c.put(req,cp)})}
        return r;
      });
    }));
  }
});
