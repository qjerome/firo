use std::os::unix::fs::OpenOptionsExt;

use crate::OpenOptions;

impl OpenOptionsExt for OpenOptions {
    fn mode(&mut self, mode: u32) -> &mut Self {
        self.ext.mode = Some(mode);
        self
    }

    fn custom_flags(&mut self, flags: i32) -> &mut Self {
        self.ext.flags = Some(flags);
        self
    }
}

#[cfg(test)]
mod test {
    use std::{
        io::Write,
        os::unix::fs::OpenOptionsExt,
        time::{Duration, Instant},
    };

    use crate::{Compression, OpenOptions};
    use std::os::unix::fs::PermissionsExt;

    #[test]
    fn test_mode() {
        let td = tempfile::tempdir().unwrap();
        let mode = 0o600;

        let mut f = OpenOptions::new()
            .trigger(Duration::from_secs(1).into())
            .mode(mode)
            .compression(Compression::Gzip)
            .create_append(td.path().join("log"))
            .unwrap();

        let start = Instant::now();

        let mut c = 0usize;
        while Instant::now().checked_duration_since(start).unwrap() < Duration::from_secs(2) {
            writeln!(f, "test").unwrap();
            c = c.saturating_add(1);
        }

        f.sync().unwrap();

        assert_eq!(f.files_sorted_by_index().unwrap().len(), 3);

        for f in f.files_sorted_by_index().unwrap() {
            let meta = f.metadata().unwrap();
            // we should also mask with umask if != 0oX00
            let exp_mode = meta.permissions().mode() & 0o777;
            assert_eq!(exp_mode, mode);
        }
    }
}
