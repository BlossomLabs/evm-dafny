"""Restore pinned Dafny and validate the crypto dependency before core verification."""
import argparse, hashlib, json, os, shutil, subprocess, tempfile, urllib.request, zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def install_dafny(destination):
    lock=json.loads((ROOT/'tools/tools.json').read_text())
    expected={p.removeprefix('dafny/'):h for p,h in lock['installed'].items() if p.startswith('dafny/')}
    if destination.exists():
        assert all((destination/p).is_file() and sha(destination/p)==h for p,h in expected.items()), 'Modified or incomplete Dafny installation'
        return destination/'dafny'
    destination.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(dir=destination.parent,prefix='.dafny-stage-') as temp:
        stage=Path(temp);archive=stage/'dafny.zip'
        with urllib.request.urlopen(lock['dafnyUrl']) as response, archive.open('wb') as output:
            shutil.copyfileobj(response,output)
        assert sha(archive)==lock['dafnySha256'], 'Dafny download hash mismatch'
        with zipfile.ZipFile(archive) as zip:
            for entry in zip.infolist():
                assert not Path(entry.filename).is_absolute() and '..' not in Path(entry.filename).parts
            zip.extractall(stage/'unpacked')
        source=stage/'unpacked/dafny'
        assert all((source/p).is_file() and sha(source/p)==h for p,h in expected.items())
        for path in source.rglob('*'):
            if path.is_file(): path.chmod(path.stat().st_mode | 0o100)
        os.rename(source,destination)
    return destination/'dafny'

def crypto():
    root=ROOT/'libs/DafnyCrypto'
    expected='b7e811d3760f70c540184c1b8d9534100ff9848f'
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==expected
    path=root/'src/dafny/util/option.dfy'
    assert sha(path)=='169ce2dc625f2bd5d05974d1911c9227abceb735187113c677c6ee51423273bf', 'Modified crypto dependency'

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--destination',type=Path,default=ROOT/'.tools/dafny')
    a=p.parse_args();crypto();print(install_dafny(a.destination.resolve()))
