"""Rebuild the two papers' offline Tectonic bundle from the official TeX archive."""

import argparse
import gzip
import hashlib
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from urllib.request import Request, urlopen
from zipfile import ZipFile, ZipInfo

HERE = Path(__file__).resolve().parent
ARCHIVE = "https://data1b.fullyjustified.net/tlextras-2022.0r0.tar"
INDEX_SHA256 = "0fb434b0fa5fdebea7f767ed9c31939c99a780d6f95cd3f540aae55910bb5697"
DEFAULT_OUTPUT = HERE / ".tectonic" / "tlextras-2022.0r0-paper.zip"
REQUEST_HEADERS = {"User-Agent": "Tectonic-paper-bundle/1.0", "Accept-Encoding": "identity"}


def read_manifest():
    assets = {}
    for line in (HERE / "tex-bundle.sha256").read_text(encoding="utf-8").splitlines():
        digest, name = line.split("  ", 1)
        if name in assets or Path(name).name != name or len(bytes.fromhex(digest)) != 32:
            raise ValueError(f"Invalid manifest entry for {name!r}")
        assets[name] = digest
    return assets


def resource_ranges(assets):
    request = Request(ARCHIVE + ".index.gz", headers=REQUEST_HEADERS)
    with urlopen(request, timeout=45) as response:
        index = gzip.decompress(response.read())
    if hashlib.sha256(index).hexdigest() != INDEX_SHA256:
        raise ValueError("Official bundle index digest changed")
    locations = {}
    for line in index.decode("utf-8").splitlines():
        name, offset, size = line.rsplit(" ", 2)
        if name in assets:
            locations[name] = (int(offset), int(size))
    missing = assets.keys() - locations.keys()
    if missing:
        raise ValueError(f"Missing from official index: {sorted(missing)}")

    # Neighbouring tar members share one HTTP request. All offsets use half-open ranges.
    groups = []
    for name, (start, size) in sorted(locations.items(), key=lambda item: item[1]):
        end = start + size
        if groups and start - groups[-1][-1][1] <= 32768 and end - groups[-1][0][0] <= 8 * 1024**2:
            groups[-1].append((start, end, name))
        else:
            groups.append([(start, end, name)])
    return groups


def download_group(group):
    start, end = group[0][0], group[-1][1]
    byte_range = f"{start}-{end - 1}"
    request = Request(ARCHIVE, headers={**REQUEST_HEADERS, "Range": "bytes=" + byte_range})
    for attempt in range(3):
        try:
            with urlopen(request, timeout=45) as response:
                partial = response.headers.get("Content-Range", "")
                if response.status != 206 or not partial.startswith("bytes " + byte_range + "/"):
                    raise OSError(f"Official server did not return byte range {byte_range}")
                block = response.read(end - start + 1)
            if len(block) != end - start:
                raise OSError(f"Incomplete byte range {byte_range}")
            return {name: block[a - start:b - start] for a, b, name in group}
        except OSError:
            if attempt == 2:
                raise


def write_bundle(output, contents, assets):
    manifest_bytes = "".join(f"{assets[n]}  {n}\n" for n in sorted(assets)).encode("utf-8")
    bundle_id = hashlib.sha256(manifest_bytes).hexdigest().encode("ascii")
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=output.parent) as work:
        archive = Path(work) / "verified.zip"
        with ZipFile(archive, "w") as bundle:
            for name in [*sorted(assets), "SHA256SUM"]:
                data = bundle_id if name == "SHA256SUM" else contents[name]
                if name != "SHA256SUM" and hashlib.sha256(data).hexdigest() != assets[name]:
                    raise ValueError(f"Official resource failed SHA-256 verification: {name}")
                # Stored entries and fixed ZIP metadata are identical across operating systems.
                info = ZipInfo(name, (2022, 1, 1, 0, 0, 0))
                info.create_system = 3
                info.external_attr = 0o100644 << 16
                bundle.writestr(info, data)
            bundle.comment = ("TeX resource subset from " + ARCHIVE).encode("ascii")
        archive.replace(output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    output = parser.parse_args().output.resolve()
    assets = read_manifest()
    groups = resource_ranges(assets)
    contents = {}
    with ThreadPoolExecutor(max_workers=6) as pool:
        for downloaded in pool.map(download_group, groups):
            contents.update(downloaded)
    write_bundle(output, contents, assets)
    print(f"{len(assets)} verified resources, {output.stat().st_size} bytes")
    print(f"SHA-256 {hashlib.sha256(output.read_bytes()).hexdigest()}")
    print(output)


if __name__ == "__main__":
    main()
